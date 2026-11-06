(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init
     ADepot_iface ADepot ADepot_init F_adepot ARepInit_kit ARepInit_A ARepInit_B ARepInit_C ARepInit_D ARepInit_E.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ARepInit () := "C59OSSVerify5KrLib5AsanW:ARepInit_A3ST0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ8AQUAR_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ@aquar_glob_constC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW7AQConst9aq_tcacheC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib5AsanW5ARepQ7aqcacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ6aintalC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ8qcoupledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ4qnumC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib5AsanW:ARepInit_BEaquar_glob_const_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_C@aqcache_loc_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_BAaqcache_glob_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_B;aintal_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_A=qcoupled_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_A9qnum_initC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ5q_locC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ6q_globC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ4q_iaC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01I59OSSVerify5KrLib5AsanW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_A2X0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ6qconc0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ARepQ7qbatchc00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib5AsanW7AQConst9AQ_GCACHEC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib5AsanW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7athreadC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib5AsanW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_A8awf_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_B<arep_rt_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_B>ainstance_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_C<athread_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_DBaregion_cells_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_D?afreearray_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_D;aslots_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_DAaslot_shadow_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_B;arelro_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_B=arep_rt2_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_DBashadow_avail_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_B=arep_rt3_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4ARep4AREPC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF5fp_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib5AsanW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_A?alayout_ok_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_E9arng_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:ARepInit_A<ablocks_initC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW4ARep5aconc00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5AsanW5ABase6ablock00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8ARepInit9AREP_initC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib2AS:MainExport8mfact_okC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00C59OSSVerify5KrLib2AS:MainExport8pfact_okC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib2AS9MainEntry8ashadow0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ARepInit_kit2LVC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5AsanW5ABase7alayout01C1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib2AS:MainExport8allow_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainExport8aallowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed4shadC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib5AsanW;AFake_iface5AFAKEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW:AFake_init:afake_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8ARepInit<AHEAP_P_initC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I59OSSVerify5KrLib5AsanW5ABase7alayout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib2AS:MainExport5mfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan>asan_mem_factsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS:MainExport5pfact00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS=MainFactsAsan?asan_pure_factsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ABase5AUMAXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C59OSSVerify5KrLib2AS=MainFactsAsan8asan_visC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8ARepInit:AQUAR_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8ARepInitAAHEAP_P_init_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW5ARepQ5AQUARC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS9MainEntry@asan_mem_facts_wC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW8F_adepot<adepot_ifaceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW<ADepot_iface6ADEPOTC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW;ADepot_init;adepot_initC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5AsanW8ARepInitFAHEAP_P_init_quar_fakeC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Init.
  Variables (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem).
  Hypothesis HM : Forall (mfact_ok asegs V m) asan_mem_facts.
  Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
  Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
  Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.   (* [comment removed for export] *)
  Hypothesis SH0 : ashadow0 V m.
  Let L := mkALayout (LV V) w U.

  (* [comment removed for export] *)
  Theorem AQUAR_init : AQUAR L (ST0 V) X0 m.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepInit ()) ["CANSEC1"; "Init"] "h01Qp;1p;5p;6p;2p;4p;3p;9g0000j1HTg000ij54Tg001bj1<Tg002cj16Tg003_j15Tg004?j62Tg0057j23Tg005nj4;Tg006gj1:Tg007\j20Tg0087j37Tg009Bl98Tg00:Hj59Tg00;Oj3GTg00<Pj2FTg00=Sj1ETg00>Rj41Tg00>mj1>Tg00?fj1?Tg00@\j1=Tg00A[j1@Tg00BUj1ATg00CLj1BTg00DLj1CTg00EAj4DTg00E[R0p,1LR1p,1VR2#HR3g00FSR4f0p,1mR5D4X00g00GKR0%<5R6P1P5%61R7g00HB#5R8g00I=#5R9g00J7R:E2R;P1P5g00JUR<P8P9P:E2R:g00KQ/35R9P1P3P4P0C;R8%:3R='0R>'0R?'0R@'0p,2HMRA9725P;P@p,2rcP2p,1wR@p,1UR;P5PAp,2HPp,2HUp,3HATM98P:P?P2P@P;P5PAD9P9P>AG25AP8P=1F12%E2C1C1C1C1C1P1P5P7%>3%?0%=3E2P1P5P<%@3%A0%B3E2%C0/35/0>'0'0,06eP1P3P4P0P5D4eCDo"). Qed.

  (* [comment removed for export] *)
  Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
  Hypothesis HQ : AQ L (ST0 V) X0 m.
  Hypothesis HS : ASEC L (ST0 V) X0 m.
  Hypothesis HD : DEP L m.
  Let H := mkAHoles AQ ASEC DEP AFK.

  Theorem AREP_init : AREP H L (ST0 V) X0 m.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepInit ()) ["CANSEC1"; "Init"] "h01ch12Hcp;1p;4p;2p;3p;5p;7p;9p;;p;:p;6g0000j1RTg00L1j4QTg00Ldj24Tg00M[j33Tg00NTj4PTg00OKj1<Tg00Oij2;Tg00PEj25Tg007\j20Tg00Paj47Tg00Q^j58Tg00RXj59Tg00SNj5:Tg00TJj1OTg00U@j1GTg00V8j4FTg00W5j1=Tg00Wmj7>Tg00Xkj5?Tg00Ymj5@Tg00[1l9ATg00\3l;BTg00];l:CTg00^@l:DTg00_Al:ETg00>Rj42Tg00`Hj36Tg00aIj3HTg00bLl;ITg00cTj3JTg00dWj5KTg00eNj5LTg00fDj3MTg00g<j6NTf6f5f4f3f2f1R0f0R1C2C2p=1p,2rcR2p,1LR3p,1VR4#RR5g00FSR6CQR7p,1mR8,43R9A3358R:P3P5P6P8CPR;g00h0R<g00hN#</;1g00i3,51'0R=P3P5P8P0C7R>P3P5P6P8P0D8R?P3P5P6P8P0D9R@P3P5P6P8P0D:RA'0RB'0RC'0[]0RDp,2AQP3P5P6P8O4REp,4ASECP3P5P6P8O4RFp,3DEPP3P8O2RG%O8RH%G8RIP3P5P8P0CF\=^0<RJ%=8RK'0RL'0RM'0RN'0RO'0RP'0RQ'0RR'0RS'0RT'0P2P4p,1wRUp,1URVp,2HPRWp,2HURXp,3HATRYF>P9PTP4PUPVP8p,2HMRTD?P:PSP4PUPVP8PTD@P;PRP2P4PUPVP8PTPWPXPYM9APDPQP>PCP2P4PUPVP8PTPWPXPYP0P1M;BP?PBP2P4PUPVP8PWPXPYP0P1M:CP@PAP2P4PUPVP8PWPXPYP0P1M:DP2P4PUPVP8PWPXPYP0P1M:EC2F1X1=X0<PEPPp,2HQPFPOp,2HSPGPNp,2HDPHPMA648TPIPLAH48TPJPKP2P4PUPVP8PWPXPYp,3SH0P0P1M;IX1=X0<AJ48TC2F1F1F1F1F1p,1HRTP3P5P6P8DKPTP3P5P6P8DLAMT38/0N'0'0,0D,0;,0:,09,07eP2PTP3P5P6P8ENeo"). Qed.

  (* [comment removed for export] *)
  Variables (lz : list (word * word)) (AL : word -> Prop).
  Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
  (* [comment removed for export] *)
  Hypothesis ASH0 : forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
    (bv_unsigned p = shad (al_space_beg L) + 536870912 * c - 4096
     \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg L) + 536870912 * c + 32768 * k)) -> AL p.
  Hypothesis HF : AFK L [] m.

  Theorem AHEAP_P_init : AHEAP_P H L (fp_ok lz AL) (ST0 V) [] m.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepInit ()) ["CANSEC1"; "Init"] "h01Xp;2p;1p;3p;6p;5p;4p;7p;;g00j3j2>Tg00k2j2=Tg0000j15Tg00kgj34Tg00g<j63Tg003_j1;Tg00l]j52Tg007\j21Tg00mVj26Tg00n0j47Tg00ngj78Tg00oll;9Tg010kj3:Tg00>Rj40Tg00EAj4<Tp,2rcR0p,1LR1'>p,2lzR2p,2ALR3'=p,1VR4#5R5541R6g011mR7P0p,1HR8P1P5f0R9p,1mR:E3P0P1P5P9g012d#;R9D2'1X07R;'6R<P8P1P9P:C7R='1R>'1P0P4p,1wR?p,1UR@p,2HPRAp,2HURBp,3HATRCF8P6P>P0P2P3P4P?P@p,3A0IPAPBPCp,4ASH0M;9P<P=P7P;g00FSR;P0P8P1P5P;P:E3P0P1P5P;P9D2g013]A:015C0C<p,2HFC0C0C0o"). Qed.
End Init.

(* [comment removed for export] *)
Corollary AHEAP_P_init_fake :
  forall (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
    32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP -> ashadow0 V m ->
    AQ (mkALayout (LV V) w U) (ST0 V) X0 m -> ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->               (* [comment removed for export] *)
       (bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c - 4096
        \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c + 32768 * k)) -> AL p) ->
    AHEAP_P (mkAHoles AQ ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepInit ()) ["CANSEC1"] "h01ph13A0Ih22ALh32AQh44ASECh54ASH0h63DEPh73HATh82HDh92HMh:2HPh;2HQh<2HSh=2HUh>3SH0h?1Uh@1VhA1chB1khC2lzhD1mhE1wp;1p;2p;3p;8p;Eg014Zj10Tg015?j1CTg015]j1ETg016@j1XTg016bj1?Tg017Bj2WTg017bj3NTg018]j3ATg019>j1MTg01:9j2JTg01:Yj1HTg01;9j2GTg00OKj12Tg01;Sj27Tg01<0j29Tg01<Mj2DTg01<jj1VTg01=`j35Tg01>:j2UTg01?4j18Tg01?nj3:Tg0000j1BTg01@hj2;Tg01ARj2@Tg01B2j1=Tg01BWj3LTg01CRj2KTg00Oij2<Tg00PEj2ITg007\j2>Tg01DMj1OTg01EJj1PTg01FBj2QTg01F\j1RTg01GXj8STg01HXlETTg01IXj1FTf0R0#0#0p=4%00#0#0#0p=1%F0#Fp=6%=0#=p=3g01J7R1g01K1g011mg00hNR2#0#4R3#0R4#0R5#0R6#CR7#ER8%C3#E#X[R3p-0R9[R:[[[R;P:\1g01Klg00h0R1[g01LK%?1R:#?1W88#?P9\8g01Lkg01Mef5R9f2R<3Ng01NZ3Ag01O^f6R=#Mg01PX3A1J:9g01Q]#H'G%46#1R6#0#4R:#2R>f8R?g01RSR@O1'7%26R6P?%6@#6#6R@#6#6O1'7'9%24P?P@O1'7'9%1:#1R:#2'Dp,2rcR@#V551f9R4/U=f=RAf:RB#8?:4?%BBg00FSRCf7RDO4PAf;RE#8?:B4%BEPCP?O4PAf<RC#8?:EBP4O21;70/@6g00J7RF551%32RG#=#3#3#3#3#3#3#0#4#1#1#1#2f?RHg01S23Lf1RI'KPEP<O1[[^081;7</@6=51F%22/<<%25,I<'>f4R5,;7R7fC#8fBR2fARJ3:#O#P%4:#1#2f3R:'7'9RK/D65511<F<%0G#4#1#1#2,<<'>17><,9K9517'>'QPHP9O1[[[^B1^A1^08PHf>R8PAPCP4P?PDP=P9P2PJf@%R@P5P:P<PEPBPIP0P@PHP8PAPCP4P?P=GSMETW5W1W8W<W;W>W7W=W:W9W2WCXD3W?WEW@W6X4;W3o"). Qed.

(* [comment removed for export] *)
Corollary AHEAP_P_init_quar_fake :
  forall (ASEC : alayout -> astate -> aconc -> amem -> Prop) (DEP : alayout -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (pfact_ok V) asan_pure_facts -> (length U <= Z.to_nat AUMAX)%nat ->
    32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP -> ashadow0 V m ->
    ASEC (mkALayout (LV V) w U) (ST0 V) X0 m -> DEP (mkALayout (LV V) w U) m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->               (* [comment removed for export] *)
       (bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c - 4096
        \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c + 32768 * k)) -> AL p) ->
    AHEAP_P (mkAHoles AQUAR ASEC DEP AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepInit ()) ["CANSEC1"] "h01ph13A0Ih22ALh34ASECh44ASH0h53DEPh63HATh72HDh82HMh92HPh:2HSh;2HUh<3SH0h=1Uh>1Vh?1ch@1khA2lzhB1mhC1wp;1p;2p;3p;8p;Cg014Zj10Tg015?j1BTg015]j1DTg016@j1WTg016bj1?Tg017Bj2VTg017bj3NTg018]j3ATg019>j1LTg01:9j2ITg01:Yj1GTg01;9j2FTg00OKj12Tg01;Sj27Tg01<0j28Tg01<Mj2ETg01<jj1UTg01=`j35Tg01>:j2TTg01?4j1=Tg01?nj3;Tg0000j1MTg01@hj2:Tg01ARj2@Tg01B2j1<Tg01BWj3KTg01CRj2JTg00Oij29Tg00PEj2HTg007\j2>Tg01DMj1OTg01EJj1PTg01FBj2QTg01T0j8RTg01TnlCSTg01IXj1CTf0R0#0#0p=4%00#0#0#0p=1%C0#Cp=6%<0#<p=3g01J7R1g01K1g011mg00hNR2#0#4R3#0R4#0R5#0R6#BR7#DR8%B3#D#W[R3p-0R9[R:[[[P:\1g01Klg00h0R1[g01LK%?1R:#?1V88#?P9\8g01Lkg01Mef5R9f2R;3Ng01NZ3Ag01O^f6R<#Lg01PX3A1I:9g01Q]#G'F%46#1R6#0#4R:#2R=f8R>g01RSR?O1'7%26R6P>%6?#6#6R?#6#6O1'7'8%24P>P?O1'7'8%1:#1R:#2'Ep,2rc#U551f9R?/T<f<R4f:R@#=?;?>%M@g00FSf7RAO4P4f;RB#=?;@?P>O21:70/@6g00J7RC551%32RD#<#3#3#3#3#3#3#0#4#1#1#1#2f>REg01S23Kf1RF'JP@P;O1[[^081:7;/@6=51C%22/9;%25,H;'>f4R5,:7R7fB#=fAf@R23;#O#P%4:#1#2f3R:'7'8RG/E655119C;%0D#4#1#1#2,9;'>17=;,8G9517'>'QPEP9O1[[[^@1^?1^08g01V3P2f?PEf=R2P4PBP@P?P>PAP<P9P5PEP2P4PBP>PAP<P9GRP:P;PFP0MCSW4W1W7W:W<W6W;W9W8W2WAXB3W=WCW>W5W3o"). Qed.

(* [comment removed for export] *)
Corollary AHEAP_P_init_qdf :
  forall (ASEC : alayout -> astate -> aconc -> amem -> Prop)
         (V : nat -> Z) (w : bool) (U : list (list Z)) (m : amem) (lz : list (word * word)) (AL : word -> Prop),
    Forall (mfact_ok asegs V m) asan_mem_facts -> Forall (mfact_ok asegs V m) (asan_mem_facts_w w) -> Forall (pfact_ok V) asan_pure_facts ->
    (length U <= 4096)%nat -> Forall (fun u => (length u <= 254)%nat) U ->
    32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP -> ashadow0 V m ->
    ASEC (mkALayout (LV V) w U) (ST0 V) X0 m ->
    (forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p) ->
    (forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->               (* [comment removed for export] *)
       (bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c - 4096
        \/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg (mkALayout (LV V) w U)) + 536870912 * c + 32768 * k)) -> AL p) ->
    AHEAP_P (mkAHoles AQUAR ASEC (ADEPOT adepot_iface) AFAKE) (mkALayout (LV V) w U) (fp_ok lz AL) (ST0 V) [] m.
Proof.
ltac2:(KReplay.run1 (kr_t_ARepInit ()) ["CANSEC1"] "h01ph13A0Ih22ALh34ASECh44ASH0h53HATh62HMh73HMwh82HPh92HSh:2HUh;3HU'h<3SH0h=1Uh>1Vh?1ch@1khA2lzhB1mhC1uhD1wp;1p;2p;3p;;p;4p;Ag014Zj12Tg015?j1FTg015]j1ETg016@j1]Tg016bj1@Tg017Bj2VTg017bj3GTg018]j3:Tg01Vij1PTg019>j1NTg01:9j2DTg01;9j2JTg00OKj14Tg01;Sj28Tg01<0j29Tg01<Mj2HTg01<jj1STg01=`j37Tg01>:j2RTg01?4j1ATg01?nj3?Tg0000j1QTg01@hj2<Tg01ARj2CTg01B2j1=Tg01BWj3MTg01CRj2OTg00Oij2;Tg00PEj2LTg007\j2>Tg01DMj1KTg01EJj1TTg01FBj2UTg01Wkj1\Tg01Xkj2[j4XTg01Yil;ZTg01ZklAWTg01IXj11Tf0R0#2#2p=6%10#1p=I%10#1#1#1p=B%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=Y%10#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0%20#2#2#2p=3%=0#=p=5g01J7g01K1g011mg00hNR1#2#6R2#2R3#2R4#2R5#FR6#ER7%F2#E#][R2p-0R8[[[[g01Klg00h0R9[g01LK%@9R:#@1V77#@P8\7g01LkR8g01MeR;f5R<f2R=3Gg01NZ3:f6R>f3R?5G;%P<5:8g01O^f7R8#Ng01PX3:1D:>g01RSR;#I#BR@#BRA#B#Y#0#0#0#0#0#0#0RB#I#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0'J1D90/JBXC:=::8%65#3R5#2#6R:#4RBf:RCP;O1'8%45R5PCPAO1'8'9%43PCP@O1'8'9%3:#3R:#4'Hp,2rcR@#S579f;R3f8RA'Rf=R;f<RD#A??3C%QDg00FSf9REO41<60/C5g00J7RF579%51RG#=#5#5#5#5#5#5#2#6#3#3#3#4f?RHg01S23Mf1RI'OP3P=O1[[^071<6=/C5=79F%41/;=%44,L='>f4R4,<6R6fC#AfBfA3?#K#T%6:#3#4/8?'9R:/H55791;F=%2G#6#3#3#4,;='>18B=,9:9796'>'UPHP<O1[[[^@9^?9^07f@%\@R7,[@PHf>R9P;PDP3PCPEP8P>P4P?P=P@PHP9P;PDPEPAP8P>P<P4M;ZP@P7%AH??9;PDCXePIP0MAWW4W1W9W<W5W;W:W8W7W6W2WAXB2W=WDW>W3o"). Qed.
End CANSEC1.
