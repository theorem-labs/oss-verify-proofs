(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocHINV Malloc_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RMalloc_iface () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad1MC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Malloc<MallocBlocks5blockC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ProgDeps4bptrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec5Monad5implMC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes4list00c59OSSVerify5KrLib5Plain=RMalloc_iface5RHEAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5stripC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState6ps_brkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib4Spec6PState4ps_mC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep5rmrepC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Malloc:MallocHINV9HINV_fromC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain:RMallocRep<ref_reservedC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I59OSSVerify5KrLib4Spec6PState6PState00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_transC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib5Plain=RMalloc_iface<rclient_addrC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK47Corelib4Init5Logic2eq01c59OSSVerify5KrLib5Plain=RMalloc_iface:rheap_presC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transK47Corelib7Numbers7BinNums8positive01c59OSSVerify5KrLib5Plain=RMalloc_iface=ralloc_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<Malloc_iface8in_blockC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_addrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocBlocks8blk_sizeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC46Stdlib5Lists4List2InK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib5Plain=RMalloc_iface=rclient_rangeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr07c59OSSVerify5KrLib5Plain=RMalloc_ifaceBrclient_range_addrC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC59OSSVerify5KrLib3Lib3Mem3mrdC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC59OSSVerify5KrLib3Lib3Mem5wr_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells8cells_wfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Cells;cells_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5CellsBcells_bytes_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMalloc_ifaceCrheap_pres_bytes_atC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMalloc_iface@rheap_pres_wr_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Cells4cell05C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3ArrArw_cells_of_u8arrC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rc59OSSVerify5KrLib5Plain=RMalloc_ifaceCrheap_pres_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3ArrAu8arr_of_rw_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Image9reservedZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6PState7ps_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>MMAP_THRESHOLDC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec3evtC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr03K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions9bv_signedC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib4StepDunsigned_Z_to_bv_addC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC59OSSVerify5KrLib3Lib8PropExec9b_addsextC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC59OSSVerify5KrLib3Lib6MState8step_genC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbK4ELinuxProcessSemantics5Riscv5Instr5instr05C59OSSVerify5KrLib3Lib6MState;lit_add_litC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics5Riscv7Prelude4tree00C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC59OSSVerify5KrLib3Lib6MState;ret_pc_foldC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Step@Z_to_bv_lit_selfC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC59OSSVerify5KrLib3Lib4Exec8evt_doneC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib4Exec8evt_stepC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00c59OSSVerify5KrLib5Plain=RMalloc_iface9RFREE_SYMC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C59OSSVerify5KrLib3Lib6MState6w0_litC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C59OSSVerify5KrLib3Lib6MState6w1_litC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib5Plain=RMalloc_iface?rfree_null_stmtC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition RMALLOC_SYM : Z := 0x1dbf4.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x1dab4.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop :=
  (RLIBC <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4)
  \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
  exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
                 /\ HINV_from ref_reserved st (ps_brk s) LB0.

Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "p'0h03LB0h11Hh22sth31mh42E1h52E2h62H1h72H2h82H3h92HPh:2LBh;1sh<2s'h=1zi001xp;1p;3p;2p;4p;6p;5p10000p4p70R0p1000ep4p710R1p8P0g001VR0p4p710R2p8g0024R3p4p70R4p10032p4p710R5p8P4g003IR4p4p710p8p10044p4p70R6P1p8P6P2p8p1004ip4p70R6P5p8P6p1005bp4p73110p8p1006Wp4p7210P2p8g007Cj1GTg007cj3;Tg008aj13Tg009Wj10Tg00:NR2j2>Tg00:hj11Tg00;]j3<Tg00<XR6j29Tg00=3j4ATP0j6DTg00=Nj4CTP4j3FTg00=hj3=Tg00>Bj5?Tf1R4f0R05F3p=2g00?BR5%107=4p=7f3R1g00@;R7f2R8P4P0D?p=@A<184/90p=41940,98p=8g00A=R9?=40p=:A=540p=6P1P7P8%04P0D?p=5A=584/90p=Ef4R:P1P7P8P4P0D?'9p=Bg00A[R7%G3R3g00BTA;140P2P5120:%34R;f6R<'7p,2rcR=P4P1P=P4%0<R>P0C@C438X03,>3X25%1:f5R?'7%0?/:>A;<?:[[P0120<f8R>#1R@,6;P=P4P?P=P4P>P0C5C438X03,>3P2P3f7R2,20%38f9RA#1RB'6P=P8P<P=P8%0AR<P0C@C438X0316@Bf:RB#0,:<A;BA>[[P0120A%3:f;R<'7P=P:P>P=P:P<P0C5C438P6124B%3?f<RB#1R@P=P?PAP=P?PBP4C5C43Ef=RC,7@%0Cf>R@#0':A;@CB[[P0121B%3>f?R@#1P=P>PBP=P>P@P:C5C43EP6%3Af@R:#1RD'6P=PAPCP=PAP:P?C5C4fAR?,7D%0?fBRD#0':A;D?:[[P0%3</7DP=PBP:P=PBfCRDP>C5C4P6A<=C?P=PCfDRCPAC5%1CfERA'7%0AfFR?#0':A;?AC[[P0A<=@DP=P:fGR?PBC5%1?fHRB'7%0BfIRA#0R6':P5fJR>,20fKRE#1RF,6;P=P4PAP=P4PEP0C5C438X03,>3X25PDP3120A%3CRE%1>R;'6A<=CBRGP=PC%0>R>P0DB38X03P@P5P;12:ARH16E0PGP=PCP>P:DB38X35P9P>16EFPGP=PCP0P:DB58HX=912@B%3D/6;R;A<=D?R?P=PDP>P@C@R@'9R>'9P<P;P>P2P?P@P1P8CACACAP6P0ED%1AP4EDCCCCW5W4W8W7P4P0O2n2001000000121000000W1W6P4P0O2n2001000000121000000W1W9P4P0O2n2001000000121000000W1X03P4P0O2n2001000000121100000W1X25P4P0O2n2001000000121100000W1W3W:X<7W;o"). Qed.

Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "p'0h03LB0h11Hh22sth32H1h42H2h52H3h62HPh72LBh83LB'h91Ph:1mh;1si001xp;1p;3p;2p;6p;4p;5g007Cj1DTg007cj34Tg008aj17Tg00:NR0j2:Tg00:hj12Tg00;]j38Tg00<XR1j26Tg00CNj6CTg00=3j4<Tg00=Nj4ATg003Ij3BTg00=hj3;Tg009Wj1?Tg00>Bj5@Tg0024R2f1R3f0R43Bp=0g00?BR5%247;3p==f6R6f5R7f4R838f3R9g00@;R:f2R;%?3P4D@'6p=11634,6;p=5%73=;54p=3A;5;3/64p=>P9P:P;%?3P4D@p=9g00A[%D2R:g00BTA49;4P0P51047%73R</=6p,2rcR=P3P9P=P3P6P4F135X0:,::X251089A4689[P4f7R>,04f8R?,=<P=P3P7P=P3P?P4F135X0:,::P0P:104?f9R0#2,3;P=P;P6P=P;P0P4F135X0:10?>f:R@?4?>[P4104@f;R>#2,38P=P8P?P=P8P>P4F135P1103>%77f<RA#2P=P7P0P=P7PAP3F13>10A>f>RB?4A>[P4f=RC,09%7?f?R9#2P=P?PAP=P?P9P8F13>P1f@R8#2,30P=P0PCP=P0P8P7F11089fBR7?489[P4%27,3>P=PAP8P=PAfCR>P?F1P1fA98=CP=PCfDRCP0C910C>fFR0?4C>[P4A8=9>P=P8fGR8PAC91080P5fIRA,04fKR9,=<P=P3fHR<P=P3P9P4F135X0:,::X25P7P:104<fJR9#2,3>P=P>P8P=P>P9P4F135X0:PB10B8%2A,37R9A8=70R0P=P7PAPBC9RA'6R7'6P2PBP<P8P@P4ECP9P7P6P0PAP;P3C<C<C<CACAW9W5W4P3P4O2n2001000000120000000W1W3P3P4O2n2001000000120000000W1W6P3P4O2n2001000000121000000W1X0:P3P4O2n2001000000121100000W1X25P3P4O2n2001000000121100000W1W:X8:W7W;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0x26000 <= a < 0x59000 /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h01Hh12LBh22SPh32_Hh43_H0h51ah61mp;1p;2p;3p;4g007Cj1BTg00D=j2ATg00DYj10Tg00E>j12Tg00E\j2@Tg00F9j2;Tg00<Xj2:Tg00FUj39Tg00GZj18Tg00H8j17Tg00H[j16Tg00I=j14Tg00=hj31Tg00Ilj35Tg00Jij1?Tg00KKj13Tg00Kdj2<Tg00=3j4=Tg00L>j4>Tg0024#Bg00A=R0g00BTg00MAf0R1'Ag00M_#0R2#2%02#0R2#0#0#0#2'@,;1':f4R3f3R4f1R539%82#7R2#6R6P4f2R7#4R8O1R9;19g00NDR:?548%?2R2516#3R8%4495:3=162#3[1<69P1X08C=W4W3X50P7P5P1P1C>eW6W2W1o"). Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h02a0h12E1h22E2h31Hh42H1h52H2h62Hah72Hch82LBh92SPh:2W1h;2W2h<1ah=2m1h>2m2h?2m3p;1p;4p;2p;3p;6g007Cj1CTg00L>j45Tg00D=j2;Tg00DYj13Tg00E>j16Tg00E\j2ATg00F9j2<Tg00<XR0j24Tg00FUj3:Tg00GZj19Tg00H8j17Tg00H[j18Tg00I=j11Tg00=hj32Tg00Jij1BTg00O9j6@Tg00=3j4=Tg00Ilj3>Tg00KKj1?Tf3R1g00NDf2R2f1R33>f0R432#?p=0g0024#Cg00A=R5g00BTR6f4R7P1P2P3C5f5R8P7P2P3C5g00MA/;4g00M_#3R9#6%39#3R9#3#3#3#6'A,<4'4f8R:f7R;;:3P7P2P3P4O3%99#7R9#8R<f6R=%12R>O1P;P>O132P<P;P>%B9R9C0P<P;%11R1P9C0['4P0P;P1O1P:P1O152<P<P:P1P9C0P<P:%17R1P9C0[P;P1O1f9R>P1O152<P<P>P1P9C0P<P:%18R1P9C0['4P4P>P1O1f:R?P1O152<P<f;R1%1=P9C0P<P1%1;R@P9C0RA[P:P;P=P8O3P?P@O1P1P@O152<P<P1%1:R:P9C0\A'4P0P1P:O1f<R0P:O152<P<P0P:P9C0P<P0%1>R>P9C0[P0P>O1f>R:P>O152<P<P:P>P9C0P<f=R>%1?R?P9C0['4P4P>P?O1P:P?O152<P<f?R?%11P9C0P<P?%10R0P9C0[P?P0O1R?fAR1P0O1R:52<P<P1P0P9C0R1P<f@RA%1>P9C0[P<P?PAP0O1P:P3P=E@P3P=P4O1O1X31C=W;W2P3P4O2n2001000000120000000b0W:W1P3P4O2n2001000000121000000b0W7W6X<5P=P8P7P2C5eW5W4X?6X>6W=W9W8o"). Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "p'0h01bh12H0h22Hch34__x1h44__x2h54__x3h61Hh72HLh82HSh92Hah:2Hbh;2Hrh<2LBh=3LB'h>2SPh?3SP'h@7__arithhA4__ffhB8__varmaphC5__withD1ahE1mhF2m'i001xp;1p;4p;2p;3p;7p;8g007Cj1KTg00L>j4JTg00D=j23Tg00DYj12Tg00E>j1=Tg00E\j2XTg00FUj3:Tg00OWj17Tg00P<j19Tg00KKj18Tg00<XR0j21Tg00QBj26Tg00RCR1j2;Tg00R]j1ITg00S<j2DTg00Sej3HTg00TNj2ZTg00U:j1YTg00UZj3WTg00V:j2GTg00VXj4VTg00W6j1UTg00WTj1TTg00X?j2CTg00Jij1STg00Xbj2OTg00Kdj2NTg00YDj2PTg00=hj3QTg00Z0j3RTg00ZOj4LTg00[Aj3FTg00[[j3BTg00\5j1?Tg00]6j1<Tg00^7j2>Tg00=3j4aTg00=Nj4`Tg00^Tj3_Tg00F9j2^Tg00^kj4]Tg00_Vj7\Tg00`:j8[Tg0024R2f1R3f0R43_p=4%24#2#2#2p=5f3R5f2R6'31^34'1p=0%24#2p=Mg00A=R7P3g00`^P4C]p=AP3g00aER8g00adR9P9g00bDR:P4g00bdF\p=@P5P8P9P9P:P6P3P4G[p=E%K2R8g00BTR;f5R<P5P3P4CJf4R=/35f7R>,44f9R?,43[^02g00MAR@P4P4g00M_RA#2RB#=%2BRC#5#='XC0A:?>3P<P6P3P1f8/36%7C#7#2#5#5#5#=RCP6P6%2A#7#7#M#7#5#5#5#=RDC0%96#8'1f:RE/66';f<RF?:E5P413?5f;RG/3=PCP=P=PDC0%9=#8'1RHf=RI/6=';g00cDRJg00d0RK#IRL#I,D71D7L1D7K5H75H7g00dO'Z%YJ3W%KJP71G76P31G75CV%U7%T7RJ%7A,C7RK1C7BRB'A,@J%S9R9PJ1C7ARA/AK,@JP91AAB,@JCECE1OJ:P4P6g00e;RJg00e[R:'N1P46=QJ:dAR7@3CLbAbBbCX37X47X57136313351365[[^37^47^57P4PGP<PFP3P>O5b@3FW2P4O1PCP5P5PDC0%95#8'116G5';P1PH16F=f>RH?:F<P4PCP<P<PDC0%9<#8'1f6RF,3IPCPFPFPDC0%9F#8'1R1f?R6/6FRF';AF1F43BW2P4O116I<g00:NP21446%?4RFP>P>%<4,>FR1C0'1X02f@?:H>P4fA,44PFP?P?P1C0'1P0fBR0,43%?3R?PEPE%<3,>?C0fDR??:0GP4145?%?=R?PIPI%<=,>?C0fE/3HPCPHPHPDC0%9H#8'1RDfGRC/6HR?';P2fH,44PFP6P6P1C0'1X02P<14<C%?<RCPHPH%<<,>CC0P6P<P3O2P4CaC`9BD?3BW;W:P3P4O2n2001000000120000000W1X02P3P4O2n2001000000121100000W1P4O1n200100000021000011000W1P4O1n200100000021100011000O3W2W9XD7P>P<P=P5CJeW7W8W6XF;WEX?7X>7X=8W<o"). Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0x26000 <= A /\ A + n <= 0x59000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
      /\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "p'0h01bh14__x1h24__x2h34__x3h42H0h57__arithh64__ffh78__varmaph85__with91Hh:4__p1h;4__x4h<4__x5h=1Ah>2H1h?2H2h@2HRhA2HahB2HbhC2LBhD2SPhE1ahF1ni001xp%0p&0p;1p;4p;2p;6p;3p;7p;8g007Cj1jTg00f;k405Tg00D=j20Tg00^7j22Tg00DYj15Tg00OWj1NTg00E>j1kTg00\5j1GTg00]6j1STg00:NS00j2_Tg00QBj2MTg00R]j1CTg00S<j2fTg00U:j1oTg00V:j2]Tg00VXj4\Tg00W6j1nTg00WTj1mTg00X?j2YTg00gAj6lTg00Jik104Tg00Xbk203Tg00Kdk202Tg00YDj2~Tg00=hj3}Tg00Z0j3|Tg00ZOj4{Tg00F9j2;Tg00[Aj3iTg00RCR0j2JTg00gej6zTg00[[j3dTg00hIj1yTg00=3j4uTg00=Nj4tTg00FUj3sTg00<XR1j28Tg00^Tj3rTg00KKj1xTg00Sej3^Tg00TNj2gTg00UZj3UTg00^kj4bTg00_Vj7aTg00hgj7cTg00`:j8qTg00iKj3pTg00ink200Tg00jQk701Tf2R2f1R3f0R4';'8p=[%N4#Np=7%54#5#5#5p=I%54#kp=D%54#5p=Q%N4#5p=:%54#Np=<1023/J4p=?f4R5f3R6'01023'J/84p=61023/84p=Zg0024R7?r34p==1023/84,86p=@1823/J4p=K10621;34'8p=Wf7R8f6R9'0f5R:/;5'810621;34'8'Jp=F10561;23'8/J4p=>10561;23'8/J4#xp=Lg00A=R;/f4p=EA^;34p=4g00cDR<g00dOR=,g3;U4p=PP5g00aER>g00adR?P?g00bDR@P6P>P?P?P@P;P2g00`^RAP3Cbg00bdRBFaP4Fcp=BP2P>P?P?P@P;P3PAP4CbPBFap=9P6P>P?P?P@P2P3P4Gqp=V1823/84p=eA^;34/g=p=3A^;349^;2p=XAU<349U<2p=hAU<349U<29U<69U<5p=1Ap;34p=TP2P>P?P?P@P;P3g00k5R=P4CbPBFap=R200;4p=AP2P>P?P?P@P3P4K01p=OP2P>P?P?P@P3P4Fcp=`1223/04p=HP;P3P=P4Cbp=wP6P>P?P?P@P2P3P>P?P?P@P4PBFaFcp=v%j7P5P6P2P3H051063RB12627[3P010:5g00M_R=#5RA#5RC#7#I#I#I#DRD/05RE1256RF%5=#7#Q#:#Q#I#I#DRGPF%5=#:#7#7#<#<#:#I#DRH%5=#:#7#7#<#:#<#7#Q#DRI%N=RJ#N#<#I#DRK'2RLP5PF%:=#7#:#7#7#Q#<#:#DRM%kCRN,2MROP5PF%5=#:#7#7#<#<#<#I#DRP%DCRQ,2PRRP5%Q=#7#Q#:#<#<#:#Q#DRS12SQRT/055?FD6D6D63Z1=48%G4RFP:12:5RU%S4,2FRV'0C@X07,_73KPDP6P6PGCWPHP6P6PLPMP6P6POPPP6P6PRPSP6P6PTGFD>DL1M863K9?96P3109:1085A[E5GPHP5P5PLPMP5P5POPPP5P5PRPSP5P5PTGFD>DLf8RE/M53Kp-0RWg00d0RX#CRY#CRZ#ER[%EYRY1f;XRX'4R\'4%o<R]'P%j<R<P;1];2P31];6C\R^%n;R_%m;R`P`P`1Y;JRJ1Y;ARaP`P>P?P?P@P:ElDB&04?RbP`1Y;=R==9`JPbA9`=aRcCVCV203`@RdP4P2g00e;Reg00e[Rf+021~42=}efdg00MA=|;3C{Rfb6b7b8X1;X2;X3;W:AZ23610361026[[^1;^2;^3;^:WP41289RW,;:P8P:PEP6P3O6b53iW9P4O110D:RePUPHPLP:PUPMPOP:PUPPPRP:10T:9?USD6D6D69ZUG1=4EPFP9129:RU/0VC@X07,_73KP010D9R0PUPGPUPHPLP9PUPMPOP9PUPPPRP910T99?USD6D6D6C@f9RU,=4PFP810WVC@X07,_7A[e:GPHP:P:PLPMP:P:POPPP:P:PRPSP:P:PTGFD>DL1MU:3K9?E:P410D8RePWPGPWPHPLP8PWPMPOP8PWPPPRP810T89?WSD6D6D6C@10U91;9GPHP9P9PLPMP9P9POPPP9P9PRPSP9P9PTGFD>DL5e0R0f:RW/M9Rg'J%CZRZ#CRh#CRi#CRj#CRk#ERl/3\Rm%CkRk#ERn%EhRh/4XRo'3Rp%Ck#ERk%EiRi=Xn['3RqPqPqPq14[XRr,3lRsPp%EZRZ9Xni,3kRtPtPtPtPmPpPqPqPqPq14ZXRu,3lRvPpAXnih,3kRw14iXRx,3kRyPwPyPm13nrRw14[Y,3nRzAXnZ[,3kR{P{P{Ps13n\R|14hY,3nR}P}P}13krR~Pm13nuPzAXnh[,3kR[14loPw14iY,3nRi13kuRuPuP~P{P{P{PzPwPmP~AXnZY14koPiP|PsPzP}P}Pz%Ej/4X,3nPmP~P}P}P}PwPvPqPqPqPqPpPmPtPtPtPtPpPsPqPqPqPqPpPmPyPuPy14lx/P]9hypD1D1D1D1D1D1D1D1D1'P'PD1D1D1'P9h[[D1D1D1D1D1D1D1D1D1D1P<P^P_P`P`P`PaP=1TaJR^9R`=DBPbP`P`P`%ADR[PaP`P`P^%AGRy%AHRp99`^%AI%AK'TRK=9`a5O`%AMRI99`^%AN,TIRN=9`a5O`%APRx99`^%AQRQ,TxRl=9`a5O`%ASRu99`^1TuQRQ=9`a5O`5``5``5``DBDBPbP`P`P[P=AR`=yDBP`P>P?P?P@P`P`PpP=AR`=KDBP`P`PIP=AR`=NDBP`P`PxP=AR`=lDBP`P`PuP=AR`=QDB5O`5O`5O`Ez5``CVCVPdPfb6b7b8X1;X2;X3;P3P4P41232CW10D2RQ1226RuPGPuPHPLP2PuPMPOP2PuPPPRP210T29?uSD6D6D6C@1;2GPHP2P2PLPMP2P2POPPP2P2PRPSP2P2PTGFD>D>g00k\[5eQ[[^1;^2;^3;P4PEPUP8P:P3O5b59i0g3dW9P4O11=4WPFPEAHE8VC@X07,_7Q00P7f;Rg,=4PFPUAHUEVC@X07A[e8GPHP8P8PLPMP8P8POPPP8P8PRPSP8P8PTGFD>DL1Mg83K9?W8P4f=,=4PFPgAHgWVC@P1f>Re,=3%G3R0f<RQ%S3,209HQg3ZPDPgPgPGCWPHPgPgPLPMPgPgPOPPPgPgPRPSPgPgPTGFD>DLf?RQ/Mg3K9?egP4f@Rg,=6%G5R0%S5,209HQe7ZQP1%G:R1/0g%S:,219HgQfBRgPDPQPQPGCWPHPQPQPLPMPQPQPOPPPQPQPRPSPQPQPTGFD>DLfCR1/MQ3K7?QP4%G8/0g%GE%SE'29H1gfERE/0g10Dg1;gGPHPgPgPLPMPgPgPOPPPgPgPRPSPgPgPTGFD>DL3eRTfFRS/MgRR'JP7fG,=4PFP11;1VC@X07PU1=US%GURSPgPg%SU,2SCWP:14Zr14h\/P]'PP<P;P;1];5P2%y;R<C\P3P;1];:P6P<C\C\P_P`P`P`1Y;CRCPa%NA,Y;,TCRA9R`aDBPbP`1T=JRJ99`APbP`A9`=CPbP`PcP`1waJCvCVCVCVPdPfb6b7b8X1;X2;X3;X;;X<;12659[B312369H5:102:P6P5P5126:CW[[[^1;^2;^3;^;;^<;P4fDPE%SWP1%GWfAP3P2O8b5CuCt9dTR3dW?W>P3P4O2n2001000010121000000W4WBP3P4O2n2001000010121000000W4X07P3P4O2n2001000010121100000W4P4O1n210100001021100011000W4P4O1n201100001021100011000As9:2eWAW@XE;XF;X=;XD;WCo"). Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at psegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at psegs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "p'0h01ih14__x1h24__x2h34__x3h41Hh53Hi0h67__arithh74__ffh88__varmaph95__with:4cstrh;5cstr0h<1oh=1Ah>1Eh?2H0h@2H1hA2HBhB2HPhC2HRhD2HihE2LBhF2SPhG2_HhH1ahI2bshJ1mhK2m'i001bi011xp;1p;4p;2p;3p;7p;6p;<p;8g007Cj1GTg00DYj1>Tg00GZj1TTg00H8j1_Tg00L>j4sTg00l9j4KTg00lnj22Tg00E>j1QTg00E\j2^Tg00D=j24Tg00mNR0j2:Tg00H[R1j1rTg00mfR2j11Tg00nFj3ATg00=hj30Tg00<XR3j2<Tg00f;j4HTg00^7j2=Tg00I=j1STg00F9R4j2FTg00Kdj2ETg00ndj4`Tg00oKj1RTg00R]j1DTg00S<j2@Tg00Sej3CTg00TNj2PTg00U:j1]Tg00UZj3OTg00V:j2NTg00VXj4\Tg00W6j1[Tg00WTj1ZTg00inj2MTg00X?j2JTg00Jij1YTg00OWj1qTg00iKj3XTg0100j3pTg00Xbj2mTg00YDj2lTg00Z0j3kTg00ZOj4iTg010Sj7hTg00KKj1;Tg011^j2gTg012@j2ITg001Vj6fTg0139j6eTg00=3j4UTg013Uj3dTg014El<jTg00^kj4VTg00_Vj7cTg00hgj7nTg00`:j8oTg00Ilj3bTg00MAR5f0R6'4p=6f1R7%16'=p=?1=76#Sp=3g00NDR8?d76p=7g014jR9g00A=R:P0P2P4g015If5R4f4R2f3R0f2R;P7P6M<jp=aP:P7g00`^P6CVp=BP7g00aER<g00adR=P=g00bDR>P6g00bdFcp=5P:P7g00k5P6CVp=LP;P<P=P=P>P7P6Fnp=WP0P<P=P=P>P;P7P6Gop=8Ab876p=9g0024#Gg00BTR<g00M_R?#>R@#>#>RA#T#_RB#GP4P2P0P;CsP8P2P;P7CKP3%60RC12B;,?0%Q@RD%>A#>#>RA#Q'^RE'412B0RF,:6%rBRGf7RH%17RI,34'7AAB2730[^09'<f8RJPHP2%1FCHP8f6RFP4P2CK[P6%6412B4,?F/4E12BFRK,:6f:RL13JI'7AABH750G[^09'<P31?HK/4E12BHRK,:6f;RMf9RN/3I'7AABJ750G[^09f<ROPMPJ%1KCHP8PLPNPJCK[P612BJ,?N/4E12BLRL,:6f>RN13OI'7AABM750G[^09f?RKPNPM%1LCH%6O12BM,?O/4ERM12BO,:6RL1=NIRP#SRQ,7KRRf=RS=AB7RT50G[^09RU'<PFPMPUP;PGf@RU/7QRM%1;RV,3KRW,7U=0G6X<GPOPP12BSRS,:7%1SRX,FIRYP7PI1E:IPSPX1E:XEaP6C`RSPY%R;RI%6VRV12BKRZ#RR[%1Z#6RZg00cDR\g00d0R]#DR^#DR_#DR`#D,@:1@:^1@:]R]5C:5C:g00dOR^'P1@:`1@:_=C:]5C:/P^%]\R^5O\3O%G\R\P:1N:;P71N:0C\R]%[:R_%Z:R`1M:5Ra1J:@R@'B,5`Rb%Y=R=P`%q?,J:Rc,L@,5`RdP=P`1J:?R?=X:cRc1M:D%TA5p:RA'B,5`P=P`1Ba?,5`P=AX:?@R@,Ba,5`1L@A,5`5W`C8C8C8C81m`>R>P6P;g00e;RAg00e[Ra'E1l6;=0AadAk:57CiR5b7b8b9X1:X2:X3:%67Ra1F;0RA1=;2RD/4E1=24Re#61FeE'<\C[[[^1:^2:^3:P6fARC,2B#1Re%14R4fBREP;P0PJPOO7b6b;b:b5PEPCPNPXPPP;PSPYPIPVP[PZP^P\P]P_P`PbP=P`PdP=1B?@,5`1L@c,5`5W`C8C8P>P5b7b8b9X1:X2:X3:1=;0R5,4;1F5D'<\A\a^1:^2:^3:P6PeP4PEP;P0O5b6b;b:b5FhO3PKPQO1PUPQO150G19UQ%YBRQ50G#;19UW=0GQ#;['<P3PUPWO1PCPWO150G19CW=0GQ#;%10,3URU,9C=0GQ#;[P1PBPGPCPUO11gB6RW1I8UR3n10110100021010000P1PBPGPEPUO1PWP3n1011010002101000050GP6PE%12,3CRCO1fCR2PCO150GfDRC13E4'9=0GQ#;%1F,32R2,9C=0GQ#;[PGfEP2O1RQP1PBPGP6PW%1H,3CRH,I8RFn10110100021010000P1PBPGfFPHO1PWPFn1011010002101000050GX<GP1PBPGPQPW1I82n10110100021010000,EGPCP2O1P7EfWGW>P7P6O2n2001000000121000000bHA0GRMePTP0P7P6O2EeXDLX09CUCUWCWAW@P7P6O2n2001000000121000000W4W?P7P6O2n2001000000121000000W4WBWIX=:XK<WJXF:WEo"). Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at psegs m A n -> rclient_range LB SP A n -> wr_at psegs m' A n.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h01ih14__x1h24__x2h34__x3h41Hh57__arithh64__ffh78__varmaph85__with91Ah:2H0h;2H1h<2HPh=2HRh>2HWh?2Hih@2LBhA2SPhB1WhC2_HhD1ahE1mhF2m'hG1np;1p;4p;2p;3p;7p;8g007Cj1OTg00L>j4eTg015kj4ATg00^7j21Tg00DYj17Tg00E>j1JTg00E\j2YTg00D=j23Tg00GZj1DTg00H8j1QTg00H[j1PTg00Jij1NTg00<XR0j2:Tg00f;j4BTg00I=j1KTg00R]j1=Tg00S<j29Tg00Sej3<Tg00TNj2ITg00U:j1XTg00UZj3HTg00V:j2FTg00VXj4WTg00W6j1VTg00WTj1UTg00inj2ETg00X?j2CTg00OWj1RTg00iKj3GTg0100j3STg00Xbj2TTg00Kdj2dTg00YDj2cTg00=hj3;Tg00Z0j3bTg00ZOj4aTg010Sj7_Tg00=3j4LTg00F9j2^Tg00Ilj3]Tg00KKj1\Tg00^kj4MTg00_Vj7[Tg00hgj7ZTg00`:j8`Tg00MAR1f0R2'3p=6f2R3f1R4/^2':p=41142#Kp=2f3R5g00NDR6?]34;;2#\p=0g00A=R7P4g00`^P2CMp=8P4g00aER8g00adR9P9g00bDR:P2g00bdF[p=5P7P4g00k5P2CMp=@P3P8P9P9P:P4P2FZp=?P5P8P9P9P:P3P4P2G`p=>g0024#Og00BTR8f5R;f4R<P5P3CeP6P<P3P4CAP0%651153g00M_R=#7R>#JR?%7>#7R@#7#7#7RA#J'YRB'3%62RC?425%D@#QR@#PRDf7RE12;4%N@R@C0[^07':f8RFPEP<P5CBP6f6RGP;P<CA[P2%6;11G;/3BA4C2GPDf:RH12F4P@C0[^07':P011EG/3BA4C2EPDf;RIf9RJ/24P@C0[^07f<RKPIPFPECBP6PHPJPFCA[P211JF/3BA4C2HPDf>R612K4P@C0[^07f?REP6PIPHCB%6K11KI/3BRIA4C2KRCPDPE1164RH#KRLP@C0[^07RM':PGPIPMP3PKPHg00cDRKg00d0RM#=RI#=RN#=RO,97197N197MRM5<75<7g00dORN'I%=O,97197I=<7M5<7/IN%XKRN5HK3H%OKRKP71F73P41F75CWRM%V7RI%U7RO1E71RP1C7>R>'8,5O%R=,C7RQ,@>,5O5?ORR%N9R9PO1C7=R==G7QRQ1E7?%DA5S7RA'8,5OP9PO18P=,5OP9AG7=>R>,8P,5O1@>A,5O5?OC>C>C>1TO:R:P2P3g00e;RAg00e[RP'd1c23=;APdAb714CaR1b6b7b8X17X27X37%64?443RP1145RA/3B%63115<R?#6?4?B[[[^17^27^37P2P6P3PEP4P;PJO6b5fBRJfAR?P6f=PHP3PNPKPMPIPOPRP918=>,5O1@>Q,5O5?OC>P:P1b6b7b8X17X27X371143R1,34?41A\P^17^27^37P2P6P3PEP4O4b5F_O3PEPLO1f@R6PLO15;DPDP6PLP@C0PDP612E3REP@C0[':P0P6PEO1P?PEO15;DPDP?PEP@C0PDP?1265P@C0R6[P6P2PJ12?<R?O1fCR<P?O15;DPDfDR?12J;P@C0PDP?12<GP@C0[P2PFPGP;O2O1WBWCP4P2O2n2001000000120000000bDX?CX07CLCLW=W>W;P4P2O2n2001000000121000000W4W:P4P2O2n2001000000121000000W4W<XG7X97XF8WEXA7W@o"). Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells psegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells psegs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h01Hh11Ah22HBh32HPh42HRh52HWh63Hwfh72LBh82SPh92csh:1mh;2m'h<1np;1p;4p;2p;6p;9g007Cj1;Tg00L>j4CTg016]j45Tg017Sj49Tg018Jj11Tg00mfj10Tg015kj43Tg00f;j42Tg019Cj16Tg01::j17Tg00l9j44Tg00DYj18Tg00GZj1<Tg00H8j1BTg00lnj2ATg01;4j2@Tg001Vj6?Tg01<5l9>Tg00=3j4:Tg01=Al9=Tg0024#;g00A=R0g00BTR1g01>J#;f5R2f4R3f3R4f2R5CCg00NDR6P3P5f1R7C5g00<XR8P6P2P4P5C9P6P2P4%15#0C3f8R9f7R:P3%14#0C2P6f6R;P2P3C5[f0R<P6P:P2P3C9P8%62P6P9P;%72C4P6f9R2P:%1;#0C3f<R;f;R8P9%1:#0C2P6f:R3P2P9C5[[P<%6:P6P8P2%79C4P6P;P3%12#0C3f?R2f>R9P8%13#0C2P6f=R:P;P8C9P6P:P;%18R=#0R>C3%68P6P:P;%78R6C4P4f@R?P2P9P:P;P6P3P5g014jR5P=fAP?P:%0<C2X<5P<g00M_#8#8#8#<#B/A61@84E?M9>C:P?P2P9P:P;P>P3P7P<M9=C:W4W5W2W6P7P<O2n2001000000120000000W0P7P<O2n2001000000120000000W0W3W9X10X;1W:W8W7o"). Qed.

Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
  rheap_pres LB SP m m' -> u8arr psegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
  u8arr psegs m' A xs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h01Ah11Hh22HPh32HRh42LBh52SPh61mh72m'h81nh92xsp;1p;4p;2p;3p;5p;6p;9g007Cj14Tg00DYj11Tg00GZj16Tg00H8j15Tg00L>j4BTg01??j4;Tg00lnj23Tg00mfj10Tg00f;j42Tg01@1j27Tg00U:j18Tg00UZj39Tg01@fj5:Tg01Adj2ATg01BDj1@Tg001Vj6?Tg018Jj1<Tg01Bhl9=Tg01D4j6>Tg0024#4g00A=R0g00BTR1g00M_#1#1#1#6#5R2#4f5R3f4R4f3R5f2R6CBg00NDR7P4P6f1R8C;f7R9f6R:P51326#0C2P7P3P41325R2P5f8R;P9P:P3P4g01>JR<1725%8<39R<P6P7P:P4P5P8D:g014jR8P2f9P;P3f0R3#0C2X88P3g00d0,A2%@2E?P;P9P4%<<#0C2eM9=E>W3W1W2W9X00X71W6W5W4o"). Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk psegs m lo hi -> SP <= lo -> stk psegs m' lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "p'0h01bi001bh11ah24__x1h34__x2h44__x3h51Hh67__arithh74__ffh84__p1h98__varmaph:5__with;1Eh<2H0h=2H1h>2HPh?2HSh@2HWhA2HbhB2HihC2LBhD2SPhE2SThF1WhG2W0hH2hihI1ihJ2lohK1mhL2m'hM1oi011xp;1p;4p;2p;3p;6p;7p;8g007Cj1RTg00L>j4nTg01E2j4FTg00D=j23Tg00DYj14Tg00E>j1BTg00E\j2[Tg00F9j26Tg00GZj1MTg00H8j1VTg00H[R0j1UTg00I=j11Tg00Jij1QTg011^j2ITg00<XR1j2:Tg00R]j1ATg00S<j2@Tg00Sej3?Tg00TNj2GTg00U:j1ZTg00UZj3ETg00V:j2NTg00VXj4YTg00W6j1XTg00WTj1WTg00X?j2DTg00OWj1<Tg00^kj4JTg00inj2LTg0100j3TTg00Xbj2STg00Kdj2mTg00YDj2lTg00=hj3;Tg00Z0j3kTg00ZOj4jTg00P<j1fTg00KKj1OTg00QBj2dTg00RCj2cTg00gAj6bTg00[Aj3`Tg00:NR2j2CTg012@j2aTg001Vj6_Tg00=Nj4eTg00=3j4HTg00Ilj3^Tg013Uj3]Tg00_Vj7gTg00hgj7\Tg00`:j8iTf0R3#4#4p=Pf2R4f1R5'3/:3p=7f3R6g00NDR7?^45;;3#Op=0A]745=;63p=21C53,:4p=8g00A=R8P5g00`^P3CJp=9P5g00aER9g00adR:P:g00bDR;P3g00bdFgp=5P4P9P:P:P;P5P3F\p=KP6P9P:P:P;P4P5P3Gip=>1653,:4p=h%43#4#4#4p==g0024#Rg00BTR<f5R=f4R>P6P4CnP7P>P4P5CFf6R?/36P1g00MAR@/3>g00M_RA#4RB#BRC%4BRD#4RE#4#PRF#B'[RG,36RH163>97=3%ME#VRE#URIf8RJ%15RK%QERLC0PIf9RM%14RN1IE3ROC2X0E78E[^18':P7P?P=P>CFP513@?f7RP,6397J3PIf;RQPKPLC0PIf<RRPNPOC2X0E78E[^1897?GP113PG163J97M3PIPRPKPLC0PIf=RSPNPOC2X0E78E[^18P7f:RTPMPJCFP313MG163Q97R3PIf?RUPKPLC0PIf@RVPNPOC2X0E78ERW[^1813@R13QGRX163R97S3RYPW[^18RW':P=PXPWP5PRP5g00cDRWg00d0RX#ARZ#AR[#AR\,@81@8[R[1@8XRX5?85?8g00dOR]'G%A\,@81@8Z=?8XRX5?8/G]%ZWRZ5EW3E%RWR\P81N84P51N86CYR^%X8R_%W8R`1D8BRB1D8ARa'9,5`P8Pag00k5Rb%<A,D8RcCJ,5`5K`%Q:RdP`1L8C%MF5T8RF,9c,5`PdP`1L8@RC/9B,5`Pd19Ca,5`P8PaPbPFCJ,5`5K`C>C>C>1S`;RFP3P4g00e;Rbg00e[RC'm1l34=;bCdAk8@5CjRCb7b9b:X28X38X481634975313@6R@Ah@6G[\H[^28^38^48P3f>RHPUP4P5P>PJO6b6fAR@/35%<D#<#4#=#=#=#B%4A#<#<#P#<#=#=#=#B,65775%f5#O':fBRA/d5'cp-0RDA?8[X/G]=EWZP\P^P_P`19cB,5`P`P9P:P:P;P=Eb5K`PdP`19ac,5`Pd19aB,5`C>C>PFPCb7b9b:X28X38X48W8A745613561346[[^28^38^48^8DP3164HPUP4PAP5PQO6b63`O3PUPKO1PVPKO15;IPIPVPKPLC0PIPVPNPLC0[':P1PVPNO1P@PNO15;IPIP@PNPLC0PIP@%16PLC0R6[PIPA%1>R>POC2X0E986EP3PAP>O1fCP>O15;IPIfDR>%1=PLC0PIP>%1?R>PLC0[PPP?P=O2PIfEP>PLC0PIfFR>%1PRPPOC2X0E78EP1PIP>PPPLC0PIfGRP%1JRJPOC2X0E,CEPIP>PJPLC0PIPP%1MRPPOC2X0E78EP3PIfHPPPLC0PIfJRP%1QPOC2X0E,CEP2PEPIfKR2%1RRRPOC2X0EPIPPPRPLC0PIP2%1SPOC2X0E78EP3PIfMRS%1HPOC2PIPS%1URUPLC0PIfNRL%1VRVPOC2X0ERH,CEPMP=O1PEPHP5PIPLPUO1P0PEPIP3PO1a7Vn101101000210100001IE45;IXMIP3PSPUO1PTE_PIPSPU1IE5C2eCeCHWAX0EP5P3O2n2001000000121101000W5WGP5P3O2n2001000000121000000b1WFW;P5P3O2n2001000000121000000b1XBYXI8CHCHW@W=P5P3O2n2001000000121000000W5W<P5P3O2n2001000000121000000W?WEW>XH8XJ8XL<WKXD8WCo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= ATOP /\ (A + n <= 0x10000 \/ 0x59000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  ATOP <= fst iv
  \/ (0x26000 <= fst iv /\ snd iv <= 0x59000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
  MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ psegs) ATOP).

Lemma raddr_exposed_big : forall s n, MMAP_THRESHOLD <= n -> raddr_exposed s n.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h01nh11sp;2p;1p;3g00D=j20Tg00:hj11Tg01Edj13Tg01F\j12Tg01GRj26Tg00=hj35Tg00[Aj34Tg00A[g00A=g01HJR0f0R1'0f1,00g00?Bf2#1g00ND#3p,2rc#2'6#135;41UW0W1o"). Qed.
Lemma raddr_exposed_init : forall s n, ps_m s = ps_m (ps_init (reservedZ psegs) ATOP) -> raddr_exposed s n.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h01nh11sp;1p;2p;3g00:hj10Tg01Edj16Tg01F\j13Tg01GRj22Tg00=hj31Tg00D=j25Tg00[[j34Tg00A[g00A=g00?BR0f1R1#0g00ND#6p,2rc#3'2#0R231g01HJ/51f2#0=102f034UW0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells psegs m' A [CB (Z.to_nat n) junk]
           /\ (raddr_exposed s n -> A = ptr_addr s' p)
       end.

Definition rmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM psegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom psegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ rw_cells psegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk psegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells psegs m (errno_addr tp) [C4 errv] ->
  mem_inv psegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM psegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom psegs)).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt psegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom psegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom psegs)).

Lemma rfree_null_spec : rfree_null_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CANSEC1"] "h01bh13ms'h21Hh35dietRh49drhs_dieth52a0h61mh71zh81Fh92a1h:2a2h;2a3h<2a4h=2a5h>2a6h?2a7h@6dietR0hA6dietR1hB6dietR2hC2fchD2gphE2rahF2s0hG2s1hH3s10hI3s11hJ2s2hK2s3hL2s4hM2s5hN2s6hO2s7hP2s8hQ2s9hR2sphS2t0hT2t1hU2t2hV2t3hW2t4hX2t5hY2t6hZ2tpp%0p;1p;2p;3p;Op;7p;5p;6p;>p;4g00DYj15Tg00GZj1DTg00H8j1fTg00OWj1>Tg006Wj2{Tg01IIj28Tg00=hj33Tg01IolOBTg01Jaj1FTg00Jij1jTg012@j1iTg01KWj71Tg01LIj3dTg00E>j17Tg00H[j1YTg01M:j1ZTg01N@j1uTg00Kdj2;Tg01OHj2kTg01P4j5TTg01P]j3RTg01QDj3QTg01RFj2PTg01SAj2OTg01Sij2ITg00^7j2ETg01Taj2JTg01UKj2eTg001Vj6:Tg01VMj3MTg01W8j3LTg01W]j3cTg011^j20Tg01XXj2bTg01YZj1aTg01ZZj2|Tg01[:j1^Tg01[kl>]Tg00=3j4\Tg01\cj1zTg01]Pj42Tg01^=j3[Tg01^jj4yTg01_Vj2wTg01`Qj1vTg01a>j2hTg0139j6gTg01a[j4tTg01b7j3rTg01bcj2WTg01cHj3GTg01cmj1qTg01dhj1pTg01efj1oTg01fGj4nTg01g=j6VTg01h3j2sTg01hoj2UTg01j7j2mTg01jjj3xTg01kMj4lTf0R0#5#5p=<%>0#>p=6%50#>p=@%>0#5p==g00NDR1/s0p=Cg01kmR2/U0p=S%50#5#5#5p=Hf3R3f2R4f1R5/m03xp=?1U25=340p=Af6R6f5R7f4R8P3P4P5P0F1,U2p=Ng00e;R9g01m4R:730p=`g01mTR;g00A=R<P5P0Clp=_P6P7P8P3P4C2P5P0C2p=4P8P31045P0C2p=9P6P7P8P3P4P5P0C2C2p=Kg00e[R=9390p=Xg00M_R>#5R?#5R@#5#<RA#5S00#DRB#fRC%>?R?#DRD/{C%DARA#fREg00BTfHRFg00MARG,8BRH53CPCPHfTRIfSRJfRRKfQRLfPRMfORNfNROfMRPfLRQP5fJRRfIRSPFfGRTfFRUfERVfDRWfCRXfBRYfARZf@R[f?R\f>R]f=R^f<R_f;R`f:Raf9Rbf8Rcf7RdP6MOBReP7%FIRfP8%jCRgP3%i1RhF19320X12PJPKPLPMPNPOPPPQfKRiP0PSPFPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP6P7MOBRjP8g01n@,8BS01P3PgP4PhF15d1X5CPHPCP1PIPJPKPLPMPNPOPPPQPHPRPSPFPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP6MOBRkP7PfP8PgP3PhF19320X12RfPjP8%6>#@#=#=#=#6#@#<#7Rl,8BRmP3PgP4PhF1RnPjP8%6>#@#=#6#6#6#=#<#7Rj,8BRoP3PgP4PhF1Rp%YCRq%Zn;3g%u2Rr%Cn%SpRp331;qgS02PpPrPr%7@R@,8BRpPDPGPD%5?R?#5#@#<Rn#5#H#H#HRs#7C?%>?#DRt%7nRnPtPnC?Rn'kRuPeP7PmP8PgDT3R=Q13,PhA3r05X6rS03PC1OtnRv,ImfURwPIPJPKPLPMPNPOPPP4PiPRPSPFPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdMOBP6P0P7PgP8PhF1=Ar5X0CRxPC1Elv,8BPxPeP7PoP8PgP3PhFN,;r1JBm/Ev,8B1elvE:AMtBn9LBmAcmtnE:PeP7PmP8PgP3PhF1#CP1PeP7PmP8PgP3PhPA%>s#=#6#6#7RsPAPsC?RsPuP@%YERe10EsRn';1b1m=3end1;9:S04%as#`d1|;<R;#YR:1_u@,0;Ru';%^s=3:udM>]E:b4C\P1PfPJPKPLPMPNPOPPPQPiPHPSPFPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP6P7MOBS05P8PoP3PgP4PhF1RfPCPCPCPCPCPC%zCRu10C7Pu10CVS06PuF410CPS07PCPuPCP^PuD9S0810CLS09PCPCPuPCPZPuD9S0:10CSS0;PCPu10CbPuFKS0<F410CJRsPCPCPCPuPCPXPuD9S0=10CiS0>PCPuPCP`PuD9S0?C2Rn10CNRmPCPCPuPCP\PuD9Rt10CTS0@PCPuPCPdPuD9RvC2S0AC2PgPCPCPCPCPuPCPWPuD9S0BPCPQPCPuPCP_PuD9S0CD9S0D10CMS0EPCPCPuPCP[PuD9S0F10CFS0GPCPuPCPcPuD9S0HC2RlC2S0I10CKRxPCPCPCPuPCPYPuD9S0J10CHRyPCPuPCPaPuD9RzC210COS0KPCPCPuPCP]PuD9S0L10CUS0MPCPuPCP6PuD9S0NC2FKF4S0OP8P9PCA[BHHR{%6>#@#6#@#6#<#H#7,8BR|%6>#@#=#6#6#6#6#<#7,8BS0Pn0100000020000S0QP3PgP4PhF1R}%Zf=3qg%Cf%S}R}53rQ02P}PrPrg01oBPD%7?PD%>>R?#>#<R}#HRf#5#=#=S0R#7C?PDPGPD%7fC?%5?S0S#>#DR?%=}#<#7R}P?P}C?R}CyRfPkP7PoP8PgDT5Rp=Q13,PhQ03PC1O?}R~,IoS0TPCPCPCPCPCPvQ0@PuC2PmPtPsPnF410CwS0UPCPCPCPuQ06PuQ07Q08F4S08Q09Q0<C2S0<PgPCPCPCPCPuQ0MPuQ0KQ0LF4S07PxPCQ0J10CRS06PzC2S0V10CIRzPCPCQ0BPyQ0CQ0EPlF4F4F4RlP6P9PCg0204S0C9[BHS0BP0ALBopS0Wn0100000020000P7PgP8PhF1=Ar5X0CPC1Ej@,8BRvPlP6P9PCQ0BQ0TP0n0100000020000P7PgP8PhF1=Ar5X0CPCPHPlP6P9PCA[BH0Q0TPvn0100000020000P7PgP8PhF1=Ar5X0CPC1Ej~,8BPlP6P9PCP{P0Pvn0100000020000P7PgP8PhF1=Ar5X0CPCPCPCPCPCQ0NQ0MPuC2Q0KQ0LPxQ0VF4PzQ0IPgPCQ0<PsPCPCQ0=PyQ0?C2PmQ0AFKF4P7Q0QP8PgP3PhFN,;r1JBo/E~,8B1ej~E:Q0Cg020YE:Q0W1wj@E:AM?B}9LBoAco?}E:PkP7PoP8PgP3PhF1#CP1PkP7PoP8PgP3PhPAQ0R#5#<#@#<#@#=#<#6#7RkPAPkC?RkPfP@10EkR},;e1b1o=3e}dQ04%ak#`d1_f@,0;Rf,;:%^k=3:fdM>]E:b4C\Q0O%vCRfP9P{P=1;<G1JBHRk93<GR}dP}P<PG1h00#XX7<1;9=PkP0Egb21hkk#Xe%X{eCtA39={P9P=fWR=fVRkPwPIPJPKPLPMPNPHPPPQPiPRPSPFPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbMOBPc%F=PdPgP6PhF19320X12P4PdP9PCP0P|Q0Pn0100000020000P6PgP7PhF15d1X09PCp-1PCPCPCQ0HQ0GPuC2Q0EQ0FPzQ0DF4PfPCPCPCPuQ0@PuC2R9PmPtC2S0@PsPnC2PfPCPCPCPCPuQ0;PuC2Q09Q0:Q0UQ08F4S0810C=S0UPCPCP9PyPtC2PsPnFKPfP1fZRffYRnfXRtP=PkPwPIPJPKPHPMPNPOPPPQPiPRPSPFPTPUPVPWPXPYPZP[P\P]P^P_MOBP`%FfR9PaPgPbPhF19320X12RmP3P3P4103nP5PgP0F4R}PaP|PbPgPcPhF1RoP}Pa%FnR}PbPgPcPhF1R?%Zo=3qg%Co%S?R?53rQ02P?PrPrPDPGPDQ00#<R?#7C?PD%7>R>PDP>C?Q0S#5#DRDPGPDPGC?Ro3rRqP8P8P3108fP4PgP5F4RjP`P|PaPgDT5Rp=Q1b,PhQ03PC1ODoRp,IfP7P7P8f[R~,07P3PgP4F4RvP_g021ORl,WB9GB0P`PgPaPhF1=Ar5X0CPC18B>R>PvP_1I~p1WB05GBP`PgPaPhF1=Ar5X0CP<1JBfR~PvP_18B01WB>R>5GBP`PgPaPhF1=Ar5X7<PCPfPvP_AGB0>P`PgPaPhF1=Ar5X0CPCP9PvP_P0P`PgPaPhF1=Ar5X0CPjP`P9PaPgPbPhFN,;rAGBf>%qfE:18B~%pfE:1E~G%o~E:Plg0224E:AMDBo9LBfAcfDoE:PjP`P|PaPgPbPhF1#CP1PjP`P|PaPgPbPhPA%>?#=#@#6#7R?PAP?C?R?PqP@10E?RE,;e1b1|=3eEdQ04%a?#`d1_q@,0;R;,;:%^?=3:;dM>]E:b4C\P1PmPCPCPCPCPCQ0?Q0>PuC2PsQ0=Q0UQ0@F410CnQ08PgPCPCPCPCPuQ06PuPxQ0JF410CkQ0710CtPCPCPCPuQ0GPuC2PyQ0FPzQ0DF4F4F4PaP}PbPgPcPhF1PnPtP=PkPwPIPJPKPLPHPNPOPPPQPiPRPSPFPTPUPVPWPXPYPZP[P\P]P^P_P`MOBPaP}PbPgPcPhF1,;2CnEVbBbAb@b3P{P0Egb2b3EVEVb3Q05P8%FJP3PgP4PhF19320X12PKPLPMPNPOPPPQPiPRPHPFPTPUPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdP6P7P8MOBP3Q01P4PgP5PhF15d1ePSP0E:W2W6WCW8XYCXXCXWCXVCXICXHCXQCXPCXOCXNCXMCXLCXKCXJCX?CX>CX=CX<CX;CX:CX9CX5CXGCXFCXUCXTCXSCXZCXDCXRCWEg022jeo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End CANSEC1.
