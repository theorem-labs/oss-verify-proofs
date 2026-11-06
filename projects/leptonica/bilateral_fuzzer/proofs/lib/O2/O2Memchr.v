(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim MuslStrlen RefMemcpyLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Memchr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2Reloc O2MemcpyBase.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2Memchr () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00i59OSSVerify5KrLib2O28O2Memchr5mchrH00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib6Common4Musl6Memchr5mchrH00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib6Common8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z6to_natC45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthC47Corelib4Init5Peano2ltC47Corelib4Init5Logic3notc59OSSVerify5KrLib2O28O2Memchr<rodata_clearC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib6Common5Reloc5Reloc8rl_deltaC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01C69OSSVerify5KrLib6Common4Musl6MemchrArodata_clear_hullC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib6Common4Musl6Memchr5mchrH01C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00C59OSSVerify5KrLib2O27O2Reloc8o2_relocC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemsTSrc_leptonica_bilateral_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00".
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) : Prop :=
  forall i, (0x12580 <= i < 0x125a0)%Z -> mem (Z_to_bv 64 i) = None.

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
Lemma mchrH_generic : forall mem s buf K n, mchrH mem s buf K n -> @Memchr.mchrH o2_reloc mem s buf K n.
Proof.
ltac2:(KReplay.run1 (kr_t_O2Memchr ()) [] "p'0h01Hh12H1h22H2h32H3h42H4h52H5h62H6h72H7h82H8h92H9h:1Kh;3bufh<1jh=3memh>1nh?1si003HK0i013HKni024Hbufi034Hn64i043Hnwi053Hnzi063Hroi074Hwini085Hzerop;1p;5p;6p;2p;4p;3p;?g0000j12Tg000Uj1?Tg0013j1@Tg001Vj1CTg0028j1QTg002XR0j5OTg003Pj6LTg004Oj28Tg004oj4GTg005gj2FTg006Ij3;Tg006cj26Tg007Mj24Tg007jj15Tg008Hj2RTg008ej2PTg009Bj1BTg009bj29Tg00:>j2NTg00:[j2ATg00;7j1<Tg00;Wj2KTg00<=j4>Tg00<Yj2JTg00=1j1ITg00=Jj1HTg00>Gj11Tg00>lj2=Tg00?lj27Tg00@Ij2:Tg00@gj2ETg00AAj6MTg00BJl?DTf0R1#2#2p=0%11#2p=3g00CI#2R2#2R3#2R4#2#0R5#?R6#@R7%?4R8#@R9#C[%Q9R:g00CnR;f4R<f3R=f2R>f1R?P1DOP0f5R0P<P=P>P?g00DLR@f6RAP0P<P=P>ELP1%C:g00EDf>RBf=RCf<RD,89CG1F:D3;166BR:/4D%54RD'R/PD/4D189C#B,4:'9f?R:,66189B#B'4%52%55'NR5'Ag00FjR2/9BP9%<:f@R:1K82RBC>,68=;;2g00GHfAR6#<,J1P9P?fCR9PBC>,68=;;2#I[]<146D/9:1A65fFR6#HP@fGR5P6fEfDP9f8R9f7R6PAP0P<P=P>P?P@P5%13R3#0#3#1#3R5#0#0#0#5R:%35#0#0#5R5g00Gg%34#1#0R4#2#1#1RD#2#3#0#5%13#1#0R3#2#1#3#1,=@R2'4,7:%1DRD#0#0#5/42/75':%3D#0#5%13#1#1#3,=@R@'4,7:':%34#0#0#0#5/4@/75':'EP1EMM?DW9W8W7W6W5W4W3W2W1P9P6PAP0P<P=P>P?P1O9n5000001000000191102107104100108105101103106W0X>;W:W;X?7W=o"). Qed.
