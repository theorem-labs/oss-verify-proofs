(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib LeptDefs LeptStructs.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2LeptStderr O2LeptBase.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2LeptBaseK () := "C69OSSVerify5KrLib6Common8Mallocng;AllocCredit8acr_sureC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure:asr_callocC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs4lctx00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc8aic_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocBase2ASC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib6Common:AllocIface7al_segsC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs3Cok00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common9Leptonica8LeptDefs1W00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC69OSSVerify5KrLib6Common8Mallocng;AllocCredit6aroomPC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure<alloc_marginC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Common5Hoare6ret_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib6Common9Leptonica8LeptDefs5c_topC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem5State;with_vmmapsC69OSSVerify5KrLib6Common9Leptonica8LeptDefs7cs_keptC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic3notC69OSSVerify5KrLib6Common8Mallocng9AllocBase4liveC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option02K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4c_A0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common5Hoare3at_C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface7round16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4c_vmC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topC69OSSVerify5KrLib6Common9Leptonica8LeptDefs5POSTMC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCredit:alloc_costC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface6al_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01I59OSSVerify5KrLib6Common8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc<al_calloc_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common:AllocIface5al_gpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica:LeptCredit>W_calloc_psureC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O2:O2LeptBase6p16_tpC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib2O2:O2LeptBase:p16_callocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib6Common8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C59OSSVerify5KrLib2O2:O2LeptBase4LL16C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C69OSSVerify5KrLib6Common8Mallocng;AllocCredit<ROOM_CREDMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng9AllocSure9ROOM_NMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica8LeptDefs4LSTKC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common8Mallocng;AllocCalloc<CALLOC_STACKC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BaseK.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL16} {P16 : O2Pins}.
Let AL_segs : al_segs = SEGS := p16_segs.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma W_calloc16_psure : forall C A m md regs (cnt sz kP pP : Z) (ret : word) (s : Z) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 10 = Z_to_bv 64 cnt -> getr regs 11 = Z_to_bv 64 sz ->
  0 <= cnt < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= cnt * sz < 2 ^ 61 ->
  aroomP A (m_vmmaps md) kP pP -> 1 <= kP -> alloc_margin (cnt * sz) + ROOM_CREDMAX <= pP -> cnt * sz <= ROOM_NMAX ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x49840 ->
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
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 0x2f6d4) m al_rom) md) S.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptBaseK ()) ["BaseK"] "h02A'h11bh22m'h35regs'h43resh53vm'h61Ah71Ch81Sh93cnth:1ih;2kPh<1lh=1mh>2mdh?2pPh@1qhA4regshB3rethC1shD2szp;3p;2p;1p;5p;8p;7p;4p;9p;Bp;6g0000j3mTg0019j3lTg002Bj3ZTg003Gj3WTg004Pj2kTg005Qj11Tg0066j1CTg006Tj1MTg0077j1LTg007Yj16Tg008>j2UTg008jj1STg009Jj1jTg00:Hj5iTg00;Lj8PTg00<Nj12Tg00<lj3:Tg00=Oj28Tg00>Hj2<Tg00>nj30Tg00?Hj23Tg00?dj2NTg00@Aj2BTg00@]j2DTg00A8j25Tg00AUj1YTg00BLj7KTg00CSj1XTg00D^j2ATg00E;j1VTg00F3j2JTg00FSj4OTg00GWj2@Tg00H4j2ITg00Hnj2TTg00J4j2HTg00J^j1RTg00K7j49Tg00L:j1hTg00L\j2QTg00M>j4gTg00NAj2fTg00O6j1eTg00P4j4cTg00Q7j1bTg00Qol9aTg00S3j1`Tg00T>j1_Tg00U;j5=Tg00V4j2?Tg00Vij3;Tg00Whj1^Tg00Y5j1dTg00Z1lB]Tg00[@j3\Tg00\9j6FTg00\Uj3[Tf0R0#1#1p=4%60#6p=>%10#6p=7%60#1p=Gg00]RR1g00^0R2700p=Ep,2ALR3p,2CLR4p,3ACRR59m349l34R63ZAW346R7,k3R8g00^NR9#1R:#1R;#1R<#1R=#4R>#CR?#MR@%C<R<#MRA#LRB[RCg00_3%6:RD#CRE/U@RFg00_ig00`b#SRG%j3RHP3P4P6g00aaRIf<RJDiRKP3P4P6PIf=RLPJf;RMf:RNGPRO%1D#2g00bXRP5:ERQ,8Nf9RR,<?RS50@RT%6D#2=:EP,8M=0@SRS132M%2:R:%2>'N,BM'DR>15LJRD,32%69#>#7#2,N:,BD'DRDP3P4P5fBRUf@RV#YPJPMFKRJ%29RW/3LRXf?RY,5V#Xg00c4'A/3LRZfAR[/5Vg00dA'3R\fCR]A:EWP'8f>R^50@R_%VYR`fE%2;=:EP'8R;%49#G#7#G#4#7#4#4#4#2,<?Ra50@RbfFA:E:P'81<?V50@R:%2=R=,J[#ER[P3P4P6fLRPCOg00eI'@g00fL'A/3URUP3P4P6fMRECO,3]Rcg00gYRdP3P4P6PIfSRef4Rff3Rgf2RhfP'IGPRi18hQf1RQ50@RjfQ/TgRk1H?g#E#RRl%L1RmP3P7fVRnPfC9%h1Ro30RpP3P7PRf5RqC9fR,5e,Q150mReP3P7P3P4P6fYRrCgf6RsC9=0moRof8Rt90@0#RP3P7PLPQC9P3P7f[PQC950m[^@@Rm1320fWR7/5n,B0'DPL1fNQO11<<2,QA50B[^:1RB1H?R/J=#ER=1H?NfXRA/57#e'AP3P4P6f]R<Cc#b'3R2P3P4P6PIf^P<fTR6f\P^M9aRnP3P4P5PVP^1@AWfZ/5r#`,@7FKRrp,2fxRAP^P7PV%_3RVD=1IY<'?R<fURY5;6[[[[[[[[[[[[[^4@^3F]5^2C^08PAfKR6%19#>#>#7#G#>#7#7#4#2,<?R?PEPVD=/?PfDR95;][[[[[[[[[[[[[\>[[[[[X<GP@%^4RGA;H<Y\r\n\2\=\B\m\o\e\p\l\k\j\i^4@^3F^5d^2C^08R8PAP6P]PEPVD=/?P=;H9[\c\U\[\:\b\`\_\\\Z\X\J\D\>\>\S\T\O\KX1@P@%d3A0@;LPAP6PGPEPVD=/?P=;H9\8\c\U\[\:[\`\_\\\Z\X\J\D\>\>\S\T\O\KX1@PAP3P4P5PIp,4PINSPMPNPRPtf7PsPqPfPgPhPQP0MB]Pap,3P16Ra9\34EFP?A[34aEFg00hPp,7AL_segsEFW8XC1XB@X?1X;1XD1X91WAW>W=W6W7o"). Qed.
End BaseK.
