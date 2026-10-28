(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Memchr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2MemcpyBase.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2Memchr () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00i5ARocqVerifyHarness?AgentSubmission2V28V2Memchr5mchrH00I6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memchr5mchrH00C47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission6Common8PropExec3rdnK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC47Corelib4Init5Logic3notc5ARocqVerifyHarness?AgentSubmission2V28V2Memchr<rodata_clearK47Corelib7Numbers7BinNums8positive01C6ARocqVerifyHarness?AgentSubmission6Common5Reloc5Reloc8rl_deltaC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C6ARocqVerifyHarness?AgentSubmission6Common4Musl6MemchrArodata_clear_hullK6ARocqVerifyHarness?AgentSubmission6Common4Musl6Memchr5mchrH01K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C5ARocqVerifyHarness?AgentSubmission2V27V2Reloc8v2_relocC5ARocqVerifyHarness@ProcessOversightJTgt_bilateral_fuzzer_ubsan1M?loaded_segmentsK47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x125b0 <= i < 0x125d0)%Z -> mem (Z_to_bv 64 i) = None.

Record mchrH (mem : word -> option byte) (s : word) (buf : list byte) (K n : Z) : Prop := MCHRH {
  (* [comment removed for export] *)
  Hbuf : rdn RSEGS mem s (length buf) = Some buf;
  (* [comment removed for export] *)
  Hwin : ((bv_unsigned s + K) / 8 * 8 + 8 <= bv_unsigned s + Z.of_nat (length buf))%Z;
  Hnw  : (bv_unsigned s + Z.of_nat (length buf) < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  HK0  : (0 <= K)%Z;
  Hzero : bv_unsigned (nth (Z.to_nat K) buf (Z_to_bv 8 0)) = 0%Z;
  Hnz  : forall j, (j < Z.to_nat K)%nat -> bv_unsigned (nth j buf (Z_to_bv 8 0)) <> 0%Z;
  (* [comment removed for export] *)
  HKn  : (K + 8 <= n)%Z;
  Hn64 : (n < 2 ^ 64)%Z;
  Hro  : rodata_clear mem }.

(* [comment removed for export] *)
Lemma mchrH_generic : forall mem s buf K n, mchrH mem s buf K n -> @Memchr.mchrH v2_reloc mem s buf K n.
Proof.
ltac2:(KReplay.run1 (kr_t_V2Memchr ()) [] "p'0h01Hh12H1h22H2h32H3h42H4h52H5h62H6h72H7h82H8h92H9h:1Kh;3bufh<1jh=3memh>1nh?1si003HK0i013HKni024Hbufi034Hn64i043Hnwi053Hnzi063Hroi074Hwini085Hzerop;1p;5p;6p;2p;4p;3p;?g0000j11Tg000Uj1@Tg0013j1>Tg001Vj1ETg0028j1STg002XR0j5OTg003Pj6MTg004Oj2:Tg004oj4HTg005gj2GTg006Ij3=Tg006cj28Tg007Mj22Tg007jj13Tg008Hj2TTg008ej2RTg009Bj1CTg009bj2<Tg00:>j2NTg00:[j2ATg00;7j1BTg00;Wj2LTg00<=j4?Tg00<Yj2KTg00=1j1JTg00=Jj1ITg00>Gj14Tg00>lj2DTg00?lj29Tg00@Ij2;Tg00@gj2FTg00AAj6PTg00BJl?QTf0R1#1#1p=0%41#1p=5%11#4p=6%41#4p=7g00CIR2#1R3#1R4#1R5#1#0R6#@R7#>R8%@5R9#>R:#E[%S:R;g00CnR<f4R=f3R>f2R?f1R@P1DOP0f5R0P=P>P?P@g00DLRAf6RBP0P=P>P?EMP1%E;g00EDf>RCf=RDf<RE,::CH1G;E3=187CR;/2E%35RE'T/RE/2E1::D#C,2;'<f?R;,871::C#C'2%33%36'NR6'Ag00FVR3/<CP:%B;f@R;1L93RCC?,89==<3g00G4fAR7#B,K1P:P@fCR:PCC?,89==<3#J[]<127E/<;1A76fFR7#IPAfGR6P7fEfDP:f8R:f7R7PBP0P=P>P?P@PAP6%02#5#6#6#5#7#0#0#3R6%02#5#6#6#7#6#0#0#3R2g00GS%45#6#0R5#1#7R;#1#5#0#3%44#7#0R4#1#7#6,DARE'2,96%4;R;#0#0#3/2E/92';%5;#0#3%44#7#5,DARA'2,96';%55#0#0#0#3/2A/92';'FP1EPM?QW9W8W7W6W5W4W3W2W1P:P7PBP0P=P>P?P@P1O9n5000001000000191102107104100108105101103106W0X><W:W;X?8W=o"). Qed.
