(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocHINV Malloc_iface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Ref Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_RMalloc_iface () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks5blockC13~~~C46Stdlib5Lists4List2hdI46Stdlib7Sorting;Permutation;Permutation00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog4bptrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5Monad5implMC13~~~I47Corelib4Init9Datatypes4list00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface5RHEAPC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5stripC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6ps_brkC13~~~I47Corelib4Init5Logic2ex00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog4ps_mC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep5rmrepC13~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocHINV9HINV_fromC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:RMallocRep<ref_reservedC13~~~I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6PState00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~C46Stdlib7Sorting;PermutationAPermutation_transC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface<rclient_addrC13~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notK47Corelib4Init5Logic2eq01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface:rheap_presC13~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref:F_syscalls5rsegsC13~~~C47Corelib4Init5Logic8eq_transK47Corelib7Numbers7BinNums8positive01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface=ralloc_staticC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<Malloc_iface8in_blockC13~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_addrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocBlocks8blk_sizeC13~~~C56Stdlib6ZArith6BinInt1Z3addC46Stdlib5Lists4List2InK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface=rclient_rangeC13~~~K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC46Stdlib5Lists4List9nth_errorC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega7EnvRing5PExpr07c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_ifaceBrclient_range_addrC13~~~K47Corelib4Init9Datatypes6option01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7seg_romC13~~~C47Corelib4Init5Logic6eq_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3mrdC13~~~C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step8rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5CellsBcells_bytes_lengthC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_ifaceCrheap_pres_bytes_atC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface@rheap_pres_wr_atC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Arr5u8arrC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell05C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3ArrArw_cells_of_u8arrC13~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rc99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_ifaceCrheap_pres_rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3ArrAu8arr_of_rw_cellsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3stkC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog9reservedZC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog7ps_initC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>MMAP_THRESHOLDC13~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC45stdpp9bitvector;definitions7Z_to_bvC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3mkRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6ret_pcC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState2MSC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr03C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C45stdpp9bitvector;definitions;bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4StepDunsigned_Z_to_bv_addC13~~~C4ELinuxProcessSemantics5Riscv7Prelude4sextC45stdpp9bitvector;definitions6bv_addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9b_addsextC13~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;lit_add_litC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init5Logic6eq_symK4ELinuxProcessSemantics5Riscv5Instr5instr04I4ELinuxProcessSemantics5Riscv7Prelude4tree00C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState;ret_pc_foldC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Step@Z_to_bv_lit_selfC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec8evt_doneC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib7StepKit<evt_step_genC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4Exec3evtC13~~~C45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K47Corelib4Init9Datatypes4prod01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface9RFREE_SYMC13~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01C4ELinuxProcessSemantics5Riscv3Sem2w0C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w0_litC13~~~C4ELinuxProcessSemantics5Riscv3Sem2w1C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib6MState6w1_litC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Ref=RMalloc_iface?rfree_null_stmtC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RMALLOC_SYM : Z := 0x9dddc.   (* [comment removed for export] *)
Definition RFREE_SYM : Z := 0x9dc9c.     (* [comment removed for export] *)
Definition RMALLOC_STACK : Z := 8192.
Definition RFREE_STACK : Z := 8192.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ralloc_static (a : Z) : Prop :=
  (RLIBC <= a < RCTX + 928) \/ (RERRNO <= a < RERRNO + 4)
  \/ (RSSP_GUARD <= a < RSSP_GUARD + 8) \/ (RGOT_SSP <= a < RGOT_SSP + 8)
  \/ (RVMLOCKC <= a < RVMLOCKC + 4).      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition RHEAP (s : PState) (LB : list block) (m : mem) : Prop :=
  exists st LB0, Permutation.Permutation LB0 LB /\ strip st = ps_m s /\ rmrep st m
                 /\ HINV_from ref_reserved st (ps_brk s) LB0.

Lemma RHEAP_ext : forall s s' LB m, RHEAP s LB m -> ps_m s' = ps_m s -> ps_brk s' = ps_brk s -> RHEAP s' LB m.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "p'0h03LB0h11Hh22sth31mh42E1h52E2h62H1h72H2h82H3h92HPh:2LBh;1sh<2s'h=1zi001xp;1p;3p;2p;4p;6p;5p10000p4p70p1001>p4p710R0p8g002HR1p4p70R2p1003^p4p710R3p8P2g0045R2p4p710p8p1004`p4p70P0p8p1005np4p70R0P3p8P0p1007:p4p73110p8g008Hj1GTg008hj3;Tg00:=j13Tg00;Lj10Tg00<ZR0j2>Tg00=4j11Tg00>@j3<Tg00?RR3j29Tg00?mj4ATg00@Hj6DTg00@fj4CTP2j3FTg00A@j3=Tg00AZj5?Tf1R2f0R45F1p=2g00C2R5%147=2p=7f3R6g00DDR7f2R8P2P4D?p=@A<682/94p=41924,98p=8g00E]R9?=24p=:A=524p=6P6P7P8%02P4D?p=5A=582/94p=Ef4R:P6P7P8P2P4D?'9p=Bg00F;R7%G1R1g00GKA;624P0P5124:%32R;f6R<'7p,4RUNpR=P2P6P=P2%0<R>P4C@C438X01,>1X25%1:f5R?'7%0?/:>A;<?:[[P4124<f8R>#1R@,6;P=P2P?P=P2P>P4C5C438X01,>1P0P1f7R0,24%38f9RA#1RB'6P=P8P<P=P8%0AR<P4C@C438X0116@Bf:RB#0,:<A;BA>[[P4124A%3:f;R<'7P=P:P>P=P:P<P4C5C438P3122B%3?f<RB#1R@P=P?PAP=P?PBP2C5C43Ef=RC,7@%0Cf>R@#0':A;@CB[[P4126B%3>f?R@#1P=P>PBP=P>P@P:C5C43EP3%3Af@R:#1RD'6P=PAPCP=PAP:P?C5C4fAR?,7D%0?fBRD#0':A;D?:[[P4%3</7DP=PBP:P=PBfCRDP>C5C4P3A<=C?P=PCfDRCPAC5%1CfERA'7%0AfFR?#0':A;?AC[[P4A<=@DP=P:fGR?PBC5%1?fHRB'7%0BfIRA#0R3':P5fJR>,24fKRE#1RF,6;P=P2PAP=P2PEP4C5C438X01,>1X25PDP1124A%3CRE%1>R;'6A<=CBRGP=PC%0>R>P4DB38X01P@P5P;12:ARH16E4PGP=PCP>P:DB38X35P9P>16EFPGP=PCP4P:DB58HX=912@B%3D/6;R;A<=D?R?P=PDP>P@C@R@'9R>'9P<P;P>P0P?P@P6P8CACACAP3P4ED%1AP2EDCCCCW5W4W8W7P2P4O2n2001000000121000000W1W6P2P4O2n2001000000121000000W1W9P2P4O2n2001000000121000000W1X01P2P4O2n2001000000121100000W1X25P2P4O2n2001000000121100000W1W3W:X<7W;o"). Qed.

Lemma RHEAP_perm : forall s LB LB' m, RHEAP s LB m -> Permutation.Permutation LB LB' -> RHEAP s LB' m.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "p'0h03LB0h11Hh22sth32H1h42H2h52H3h62HPh72LBh83LB'h91Ph:1mh;1si001xp;1p;3p;2p;6p;4p;5g008Hj1DTg008hj34Tg00:=j17Tg00<ZR0j2:Tg00=4j12Tg00>@j38Tg00?RR1j26Tg00H]j6CTg00?mj4<Tg00@fj4ATg0045j3BTg00A@j3;Tg00;Lj1?Tg00AZj5@Tg002HR2f1R3f0R43Bp=0g00C2R5%247;3p==f6R6f5R7f4R838f3R9g00DDR:f2R;%?3P4D@'6p=11634,6;p=5%73=;54p=3A;5;3/64p=>P9P:P;%?3P4D@p=9g00F;%D2R:g00GKA49;4P0P51047%73R</=6p,4RUNpR=P3P9P=P3P6P4F135X0:,::X251089A4689[P4f7R>,04f8R?,=<P=P3P7P=P3P?P4F135X0:,::P0P:104?f9R0#2,3;P=P;P6P=P;P0P4F135X0:10?>f:R@?4?>[P4104@f;R>#2,38P=P8P?P=P8P>P4F135P1103>%77f<RA#2P=P7P0P=P7PAP3F13>10A>f>RB?4A>[P4f=RC,09%7?f?R9#2P=P?PAP=P?P9P8F13>P1f@R8#2,30P=P0PCP=P0P8P7F11089fBR7?489[P4%27,3>P=PAP8P=PAfCR>P?F1P1fA98=CP=PCfDRCP0C910C>fFR0?4C>[P4A8=9>P=P8fGR8PAC91080P5fIRA,04fKR9,=<P=P3fHR<P=P3P9P4F135X0:,::X25P7P:104<fJR9#2,3>P=P>P8P=P>P9P4F135X0:PB10B8%2A,37R9A8=70R0P=P7PAPBC9RA'6R7'6P2PBP<P8P@P4ECP9P7P6P0PAP;P3C<C<C<CACAW9W5W4P3P4O2n2001000000120000000W1W3P3P4O2n2001000000120000000W1W6P3P4O2n2001000000121000000W1X0:P3P4O2n2001000000121100000W1X25P3P4O2n2001000000121100000W1W:X8:W7W;o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rclient_addr (LB : list block) (SP : Z) (a : Z) : Prop :=
  SP <= a \/ (0xb2000 <= a < 0xec000 /\ ~ ralloc_static a) \/ in_block LB a.

Definition rheap_pres (LB : list block) (SP : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> rclient_addr LB SP a ->
    m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None).

Lemma rheap_pres_refl : forall LB SP m, rheap_pres LB SP m m.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h01Hh12LBh22SPh32_Hh43_H0h51ah61mp;1p;2p;3p;4g008Hj1BTg00ILj2ATg00Ihj10Tg00JMj12Tg00Jkj2@Tg00KHj2;Tg00?Rj2:Tg00Kdj39Tg00M@j18Tg00M^j17Tg00NAj16Tg00Ncj14Tg00A@j31Tg00Okj35Tg00Phj1?Tg00QJj13Tg00Qcj2<Tg00?mj4=Tg00R=j4>Tg002H#Bg00E]R0g00GKg00SWf0R1'Ag00T5#0R2#2%02#0R2#0#0#0#2'@,;1':f4R3f3R4f1R539%82#7R2#6R6P4f2R7#4R8O1R9;19g00TZR:?548%?2R2516#3R8%4495:3=162#3[1<69P1X08C=W4W3X50P7P5P1P1C>eW6W2W1o"). Qed.

Lemma rheap_pres_trans : forall LB SP m1 m2 m3,
  rheap_pres LB SP m1 m2 -> rheap_pres LB SP m2 m3 -> rheap_pres LB SP m1 m3.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h02a0h12E1h22E2h31Hh42H1h52H2h62Hah72Hch82LBh92SPh:2W1h;2W2h<1ah=2m1h>2m2h?2m3p;1p;4p;2p;3p;6g008Hj1CTg00R=j45Tg00ILj2;Tg00Ihj13Tg00JMj16Tg00Jkj2ATg00KHj2<Tg00?RR0j24Tg00Kdj3:Tg00M@j19Tg00M^j17Tg00NAj18Tg00Ncj11Tg00A@j32Tg00Phj1BTg00Ulj6@Tg00?mj4=Tg00Okj3>Tg00QJj1?Tf3R1g00TZf2R2f1R33>f0R432#?p=0g002H#Cg00E]R5g00GKR6f4R7P1P2P3C5f5R8P7P2P3C5g00SW/;4g00T5#3R9#6%39#3R9#3#3#3#6'A,<4'4f8R:f7R;;:3P7P2P3P4O3%99#7R9#8R<f6R=%12R>O1P;P>O132P<P;P>%B9R9C0P<P;%11R1P9C0['4P0P;P1O1P:P1O152<P<P:P1P9C0P<P:%17R1P9C0[P;P1O1f9R>P1O152<P<P>P1P9C0P<P:%18R1P9C0['4P4P>P1O1f:R?P1O152<P<f;R1%1=P9C0P<P1%1;R@P9C0RA[P:P;P=P8O3P?P@O1P1P@O152<P<P1%1:R:P9C0\A'4P0P1P:O1f<R0P:O152<P<P0P:P9C0P<P0%1>R>P9C0[P0P>O1f>R:P>O152<P<P:P>P9C0P<f=R>%1?R?P9C0['4P4P>P?O1P:P?O152<P<f?R?%11P9C0P<P?%10R0P9C0[P?P0O1R?fAR1P0O1R:52<P<P1P0P9C0R1P<f@RA%1>P9C0[P<P?PAP0O1P:P3P=E@P3P=P4O1O1X31C=W;W2P3P4O2n2001000000120000000b0W:W1P3P4O2n2001000000121000000b0W7W6X<5P=P8P7P2C5eW5W4X?6X>6W=W9W8o"). Qed.

Lemma rheap_pres_weaken : forall LB LB' SP SP' m m',
  rheap_pres LB SP m m' -> SP <= SP' -> (forall b, In b LB' -> In b LB) -> rheap_pres LB' SP' m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "p'0h01bh12H0h22Hah32Hch46__sat1h54__x1h64__x2h74__x3h81Hh92HLh:2HSh;2Hbh<2Hrh=2LBh>3LB'h?2SPh@3SP'hA7__arithhB4__ffhC6__sat0hD8__varmaphE5__withF1ahG1mhH2m'i001xp;1p;4p;2p;3p;7p;8g008Hj1LTg00R=j4NTg00ILj20Tg00Ihj13Tg00JMj1?Tg00Jkj2YTg00Kdj3:Tg00VJj15Tg00Voj19Tg00QJj18Tg00?RR0j22Tg00XLj27Tg00YeR1j2;Tg00Z?j2\Tg00KHj2DTg00Zgj3[Tg00[Kj2ZTg00Qcj2KTg00[lj1ITg00\Kj2CTg00]4j3HTg00]]j2XTg00^Ij1WTg00^ij3VTg00_Ij2FTg00_gj4UTg00`Ej1TTg00`cj1QTg00aNj2BTg00Phj1PTg00b1j2OTg00bSj2RTg00A@j3STg00c?j3dTg00c^j4cTg00dPj3MTg00djj3ETg00eDj1<Tg00f]j1=Tg00h6j2>Tg00?mj4bTg00@fj4aTg00hSj3^Tg00hjj4]Tg00iUj7_Tg00j9j8`Tg002HR2f1R3f0R43^p=4%34#3#3#3p=6f3R5f2R6'01D34'2p=1%34#3p=Gg00E]R7P3g00j]P4C]p=@P3g00kDR8g00kcR9P9g00lCR:P4g00lcF_p=AP5P8P9P9P:P6P3P4G`p=J%L2R8g00GKR;f5R<P5P3P4CNf4R=/05f7R>,44f9R?,43[^02g00SWR@P4P4g00T5RA#3RB#?RC%3B#6#?RD'YREC1A:?>3P<P6P3P1f8RF/06%5B#5#G#5#3#6#6#6#?RGP6P6%5ARH#5#3#5#5#G#6#6#6#?RIC1%96#8'2f:RJ/76';f<RK?:J5P410?5f;RL/0=PGP=P=PIC1%9=#8'2RMf=RN/7=';1\CD1D@CRO10@D1D@E[RP[10@CRQg00mCRRA[CD3UW210@E\R^2QP3g00m_1Z@C'KPOeO1PPg00nERPg00o1RO#IRC#I,C71C7C1C7O5H75H7g00oP'X%WP3V%LPP71F76P31F75CU%T7%Q7RP1B7HRH1B7BRB'@,AP%P9R9PP1B7ARA/@H,APP91@AB,APCJCJ1OP:P4P6g010<RPg010\R:'K1R46=SP:dAd7@3CcbBbDbEX57X67X77106310351065[[^57^67^77P4f>R6PFf?RFP=PJO5bAb4bCb43MW3P4O1PGP5P5PIC1%95#8'217L5';P1PM17K=A:6K<P4PGP<P<PIC1%9<#8'2f6RK,0NPGPKPKPIC1%9K#8'2RM17FKRK';AMMK43EW3P4O117N<g00<ZP2144F%<4RKP>P>%=4,>KRMC1'2X02f@?:6>P4fA,44PKP?P?PMC1'2P0fBR0,43%<3R?PJPJ%=3,>?C1fDR??:0LP4145?%<=R?PNPN%==,>?C1fE/06PGP6P6PIC1%96#8'2RIfGRG/76R?';P2fH,44PKPFPFPMC1'2X02P<14<G%<<RGP6P6%=<,>GC1PFP<P3O2P4CbCa9EI?3EW<W;P3P4O2n2001000000121000000W1X02P3P4O2n2001000000121100000W1P4O1n200100000021100011000W1P4O1n200100000021100011000O3W3W2XF7P>P<P=P5CNeW9W:W8XH;WGX@7X?7X>8W=o"). Qed.

(* [comment removed for export] *)
Definition rclient_range (LB : list block) (SP : Z) (A n : Z) : Prop :=
  SP <= A
  \/ (0xb2000 <= A /\ A + n <= 0xec000 /\ (A + n <= RLIBC \/ RCTX + 928 <= A) /\ (A + n <= RERRNO \/ RERRNO + 4 <= A)
      /\ (A + n <= RSSP_GUARD \/ RSSP_GUARD + 8 <= A) /\ (A + n <= RGOT_SSP \/ RGOT_SSP + 8 <= A)
      /\ (A + n <= RVMLOCKC \/ RVMLOCKC + 4 <= A))
  \/ (exists b, In b LB /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b).

Lemma rclient_range_addr : forall LB SP A n a,
  rclient_range LB SP A n -> A <= a < A + n -> rclient_addr LB SP a.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "p'0h01bh14__x1h24__x2h34__x3h42H0h57__arithh64__ffh78__varmaph85__with91Hh:4__p1h;4__x4h<4__x5h=1Ah>2H1h?2H2h@2HRhA2HahB2HbhC2LBhD2SPhE1ahF1ni001xp%0p&0p;1p;4p;2p;6p;3p;7p;8g008Hj1iTg011<k405Tg00ILj21Tg00h6j23Tg00Ihj16Tg00VJj1>Tg00JMj1jTg00eDj1HTg00f]j1RTg00<ZS00j2`Tg00XLj2NTg00[lj1CTg00\Kj2fTg00^Ij1nTg00_Ij2_Tg00_gj4^Tg00`Ej1mTg00`cj1lTg00aNj2VTg012Yj6kTg00Phk104Tg00b1k203Tg00Qck202Tg00bSj2~Tg00A@j3}Tg00c?j3|Tg00c^j4{Tg00KHj2<Tg00dPj3hTg00YeR0j2MTg013=j6yTg00djj3cTg013aj1xTg00?mj4tTg00@fj4rTg00Kdj3sTg00?RS01j29Tg00hSj3qTg00QJj1wTg00]4j3bTg00]]j2gTg00^ij3QTg00hjj4\Tg00iUj7ZTg014?j7aTg00j9j8pTg014cj3oTg015Fk200Tg015ik701Tf2R1f1R2f0R3'<'9p=[%63#>p=:%63#6#6#6p=G%63#jp=B%>3#6p=;%>3#>p=]%63#6p=P1112/M3p=Df4R4f3R5'11112'M/93p=41112/93p=Yg002HR6?q23p=@1112/93,95p=?1912/M3p=J11511<23'9p=Uf7R7f6R8'1f5R9/<4'911511<23'9'Mp=F11451<12'9/M3p=511451<12'9/M3#wp=Kg00E]R:/f3p=AAb:23p=7g00nER;g00oPR<,g2;Q3p=WP4g00kDR=g00kcR>P>g00lCR?P5P=P>P>P?P:P1g00j]R@P2C\g00lcRAFZP3Fap=eP1P=P>P>P?P:P2P@P3C\PAFZp=8P5P=P>P>P?P1P2P3Gpp=T1912/93p=dAb:23/g<p=2Ab:239b:1p=SAQ;239Q;1p=zAQ;239Q;19Q;59Q;4p=0Ao:23p=LP8P=P>P>P?P9P=P>P>P?P:P4P@P5C\PAFZP1P=P>P>P?P:P2g016MR@P3C\PAFZFap=O200:3p==P1P=P>P>P?P2P3K01p=EP1P=P>P>P?P2P3Fap=X1312/13p=IP:P2P@P3C\p=vP5P=P>P>P?P1P2P=P>P>P?P3PAFZFap=u%i6P4P5P1P2H051152S0213517[2P01194g00T5RA#6R@#>S03#>R<#6#:#G#G#G#BRB/14RC1345RD%>ARE#>#:RF#;#G#G#G#BRGPD%6FRF#]RH#6RI#:#:RJ#;#;#P#BRK%;I#P#;#;#P#BRI%6F#P#BRF'3RLP4PD%6E#:#:#:#]#]#P#]#;#BRM%6@RN#jRO,3MRPP4PD%:J#;#P#BRJ%BNRQ,3JRRP4PD%><#G#:#:#:#G#BR<13<QRSP4%>H#;#P#:#;#;#BRH13HORT/145DDD4D4D4D43Y1@37%H3RDP91394RU%R3,3DRV'1C?X06,`63JPBP5P5PGCUPKP5P5PLPMP5P5PPPJP5P5PRP<P5P5PSPHP5P5PTGFD5D5DK1N753J9D85P211891174A[C4GPKP4P4PLPMP4P4PPPJP4P4PRP<P4P4PSPHP4P4PTGFD5D5DKf8RC/N43Jp-0RWg00o1RX#CRY#CRZ#AR[%AYRY1f:XRX'7R\'7%n;R]'W%i;R;P:1_:1P21_:5C^S04%m:S05%l:R^P^P^1V:ERE1V:@R@P^P=P>P>P?P9EkDe&04>R_P^1V:ARA=8^EP_A8^A@S06CTCT203^?R`P3P1g010<Rag010\Rb+021~31=}abdg00SW=|:2C{Rbb6b7b8X1:X2:X3:W:AY12511251115[[^1:^2:^3:^:WP31378RW,<9P7P9PCP5P2O6b53hW9P3O111B9RaPUPKPLP9PUPMPPP9PUPJPRP9PUP<PSP911T99DUHD4D4D4D49YUG1@3CPDP81389RU/1VC?X06,`63JP011B8R0PUPGPUPKPLP8PUPMPPP8PUPJPRP8PUP<PSP811T89DUHD4D4D4D4C?f9RU,@3PDP711WVC?X06,`6A[a9GPKP9P9PLPMP9P9PPPJP9P9PRP<P9P9PSPHP9P9PTGFD5D5DK1NU93J9DC9P311B7RaPWPGPWPKPLP7PWPMPPP7PWPJPRP7PWP<PSP711T79DWHD4D4D4D4C?11U81<8GPKP8P8PLPMP8P8PPPJP8P8PRP<P8P8PSPHP8P8PTGFD5D5DK5d0R0f:RW/N8Rc'M%CZRZ#CRd#CRe#CRf#CRg#CRh#ARi/2\Rj%ChRh#ARk%AeRe/7XRl'2Rm%Ch#ARh%AfRf/7XRn'2RoPoPoPo17[Y,2kRp17[XRq,2iRrPmPoPoPoPo%AZRZ=Sk[,2hRsPjPmPoPoPoPoPp17ZXRt,2iRuPmPoPoPoPo%AdRd=Sk[,2hRvPjPmPoPoPoPoPpPrPmPoPoPoPoPsPjPmPoPoPoPoPp17dXRw,2iS07PmPoPoPoPoASkfe,2hPj12ktRx17eY,2kRyASked,2hRzPzPzPpPr12k\R{PsPsPsPsPsPj%Ag/7X,2kRXPy17ZY,2kRgPgPgPpPuP{PvPvPvPvPvPjPX17dY,2kR|12hlR}P|P}PpPrP{PsPsPsPsPsPjPxPgPgPg12hwRwPp12ilP{ASkf[,2hRl12hqR~PlP~PlPpPwPwP}ASkfYPxPjPsPsPsPsPsP{PrPpPgPgPgPgPXPjPvPvPvPvPvP{PuPp17htP|PyPyPXPjPsPsPsPsPsP{PrPpPzPzPzPyPxPjPyP~ASke[,2hRhP~PhP{Q07PpPoPoPoPoPmPjPsPoPoPoPoPmPrPpPoPoPoPoPmPjPvPoPoPoPoPmPuPpPoPoPoPoPmPjPsPoPoPoPoPmPrPpPoPoPoPoPmPjP~PoPoPoPo12in=zm]D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0'WD0D0D0D0D0D0'WD0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0D0P;Q04Q05P^P^P^P@PAP^PA1L@ERmFOP_P^P^P^%=BRnP@P^P^Pm%=GRi%=KRo98^m%=I%=F'LRF=8^@5E^%=MRI98^m%=ORO,LIR~=8^@5E^%=JRj98^m%=QRQ,LjRp=8^@5E^%=<Rr98^m1LrQRQ=8^@5E^%=HRs98^m1LsORO=8^@5E^5X^5X^5X^5X^DeDeP_P^P^PnPAP^PAPiFOP^P=P>P>P?P^P^PoPAP^PAPFFOP^P^PIPAP^PAP~FOP^P^PjPAP^PAPpFOP^P^PrPAP^PAPQFOP^P^PsPAP^PAPOFO5E^5E^5E^5E^Ey5X^CTCTP`Pbb6b7b8X1:X2:X3:P2P3P31321CU11B1RO1315RsPGPsPKPLP1PsPMPPP1PsPJPRP1PsP<PSP111T19DsHD4D4D4D4C?1<1GPKP1P1PLPMP1P1PPPJP1P1PRP<P1P1PSPHP1P1PTGFD5D5D5g0174[5dO[[^1:^2:^3:P3PCPUP7P9P2O5b59h0c3cW9P3O11@3WPDPCAIC7VC?X06,`6Q00P6f;Rc,@3PDPUAIUCVC?X06A[a7GPKP7P7PLPMP7P7PPPJP7P7PRP<P7P7PSPHP7P7PTGFD5D5DK1Nc73J9DW7P3f=,@3PDPcAIcWVC?Q01f>Ra,@2%H2R0f<RO%R2,309IOc3YPBPcPcPGCUPKPcPcPLPMPcPcPPPJPcPcPRP<PcPcPSPHPcPcPTGFD5D5DKf?RO/Nc3J9DacP3f@Rc,@5%H4R0%R4,309IOa7YOQ01%H9Ra/1c%R9,3a9IcOfBRcPBPOPOPGCUPKPOPOPLPMPOPOPPPJPOPOPRP<POPOPSPHPOPOPTGFD5D5DKfCRa/NO3J7DOP3%H7/1c%HC%RC'39IacfERC/1c11Bc1<cGPKPcPcPLPMPcPcPPPJPcPcPRP<PcPcPSPHPcPcPTGFD5D5DK3dRTfFRH/NcRS'MP6fG,@3PDPa1<aVC?X06PU1@UH%HURHPcPc%RU,3HCUP917Zq17d\/W]'WP;P:P:1_:4P1%x:R;C^P2P:1_:9P5P;C^C^Q05P^P^P^1V:NRNP@P^P@Q03,V:,LNR;FOP_P^1LAERE98^;P_P^A8^ANP_P^Q06P^1v@ECuCTCTCTP`Pbb6b7b8X1:X2:X3:X;:X<:Q0213547[213259I491119P5P4P41359CU[[[^1:^2:^3:^;:^<:P3fDPC%RWPa%HWfAP2P1O8b5CtCr9cTS3cW?W>P2P3O2n2001000010121000000W4WBP2P3O2n2001000010121000000W4X06P2P3O2n2001000010121100000W4P3O1n210100001021100011000W4P3O1n201100001021100011000As891eWAW@XE:XF:X=:XD:WCo"). Qed.

Lemma rheap_pres_bytes_at : forall LB SP m m' A bs,
  rheap_pres LB SP m m' -> bytes_at rsegs m A bs -> rclient_range LB SP A (Z.of_nat (length bs)) ->
  bytes_at rsegs m' A bs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "p'0h01ih16__sat3h24__x1h34__x2h44__x3h51Hh62Hah73Hi0h87__arithh94__ffh:6__sat2h;8__varmaph<5__with=4cstrh>5cstr0h?1oh@1AhA1EhB2H0hC2H1hD2HBhE2HPhF2HRhG2HihH2LBhI2SPhJ2_HhK1ahL2bshM1mhN2m'i001bi011xp;1p;4p;2p;3p;7p;6p;<p;8g008Hj1LTg00Ihj1?Tg00M@j1XTg00M^j1^Tg00R=j4vTg017Qj4JTg018_j22Tg00JMj1PTg00Jkj2]Tg00ILj25Tg019?R0j2<Tg00NAR1j1uTg019WR2j11Tg01:7j3CTg00A@j30Tg00?RR3j29Tg011<j4HTg00h6j2:Tg00Ncj1TTg00KHR4j28Tg00Qcj2BTg01:Uj4bTg01;<j1QTg00Z?j2aTg00Zgj3`Tg00[Kj2_Tg00[lj1ETg00\Kj2@Tg00]4j3FTg00]]j2OTg00^Ij1\Tg00^ij3NTg00_Ij2MTg00_gj4[Tg00`Ej1ZTg00`cj1tTg015Fj2YTg00aNj2KTg00Phj1WTg00VJj1sTg014cj3VTg01;aj3rTg00b1j2qTg00bSj2pTg00c?j3oTg00c^j4nTg01<Dj7mTg00QJj1;Tg01=fj2jTg01>Hj2ITg00@Hj6iTg01?Sj6kTg00?mj4STg01?oj3hTg01A8l<lTg00hjj4RTg00iUj7gTg014?j7fTg00j9j8eTg00Okj3dTg00SWR5f0R6'5p=4f1R7%16':p=A1:76#Tp=3g00TZR8?h76p=7g01A]R9g00E]R:P0P2P4g01B<f5R4f4R2f3R0f2R;P7P6M<lp=cP:P7g00j]P6CRp=DP7g00kDR<g00kcR=P=g00lCR>P6g00lcFgp=6P:P7g016MP6CRp=GP;P<P=P=P>P7P6Ffp=UP0P<P=P=P>P;P7P6Gep=>Ad876p==g002H#Lg00GKR<g00T5R?#?R@#?#?RA#X#^RB#LP4P2P0P;CvP8P2P;P7CJP3%40RC12B;,A0%P@RD%?A#?#?RA#PRE']RF'512B0RG,<6%uBRHf7RI%17RJ,34'7ACB2730[^09'9f8RKPIP2%1GCHP8f6RGP4P2CJ[P6%4412B4,AG/5F12BGRL,<6f:RM13KJ'7ACBI750H[^09'9P31AIL/5F12BIRL,<6f;RNf9RO/3J'7ACBK750H[^09f<RPPNPK%1LCHP8PMPOPKCJ[P612BK,AO/5F12BMRM,<6f>RO13PJ'7ACBN750H[^09f?RLPOPN%1MCH%4P12BN,AP/5FRM12BP,<6RQ1:OJRR#TRS,7LRTf=RU=CB7RV50H[^09RW'9PGPMPWP;PHf@RW/7SRM%1;RX,3LRY,7W=0H6X?HPPPR12BURU,<7%1URP,8JRZP7PJ1B:JPUPP1B:PEcP6CbRUPZ%Q;RJ%4XRX12BLR[#QR\%1[#4R[1aDER]185DR^%4E185F[R_[R`%4DRag00mCRbA`DE7UW6RE%4F\b^6aRaP7g00m_1_5D'BP^eO1R^P_g00nERbg00o1Rc#ERd#ERe#ERf#E,@:1@:d1@:cRc5F:5F:g00oPRd'O1@:f1@:e=F:c5F:/Od%\bRd5Nb3N%LbRbP:1M:;P71M:0C[Rc%Z:Re%t:Rf1Y:5Rg1K:@R@'D,6fRh%W=R=Pf%s?,K:Ri,G@,6fRjP=Pf1K:?R?=V:iRi1Y:D%XA5r:RA'D,6fP=Pf1Dg?,6fP=AV:?@R@,Dg,6f1G@A,6f5UfC>C>C>C>1qf>R>P6P;g010<RAg010\Rg'B1p6;=0AgdAo:57CnR5b9b;b<X2:X3:X4:%47Rg18;0RA1:;2RD/5F1:24Rk#418kF'9\C[[[^2:^3:^4:P6fDRC,2B#1Rk%1KRKfERFP4PGPNPLO7b8b1b:b1b>b=b7fBRNfARlPOPPPRP;PUPZPJPXP\P[P]P`PEPaP^P_PdPbPcPePfPhP=PfPjP=1D?@,6f1G@i,6f5UfC>C>P>P5b9b;b<X2:X3:X4:1:;0R5,5;185D'9\A\g^2:^3:^4:P6PkPKPFP4PGO5b8b1b:b1b>b=b7FmO3PLPSO1PWPSO150H1=WS%WBRS50H#;1=WY=0HS#;['9P3PWPYO1PlPYO150H1=lY=0HS#;%10,3WRW,=l=0HS#;[P1PBPHPlPWO11jB6RY1I8WR3n10110100021010000P1PBPHPNPWO1PYP3n1011010002101000050HP6PN%12,3lRlO1fCR2PlO150H%14,3N,=C=0HS#;%1G,32R2,=C=0HS#;[PHPFP2O1RFP1PBPHP6PY%1I,3CRI,I8RSn10110100021010000P1PBPHfFPIO1PYPSn1011010002101000050HX?HP1PBPHPFPY1I82n10110100021010000,BHPCP2O1P7EiWJWAP7P6O2n2001000000121000000bKA0HTMePVP0P7P6O2EkXGQX09CSCSWFWDWCP7P6O2n2001000000121000000W5WBP7P6O2n2001000000121000000W5WEWLX@:XN<WMXI:WHo"). Qed.

Lemma rheap_pres_wr_at : forall LB SP m m' A n,
  rheap_pres LB SP m m' -> wr_at rsegs m A n -> rclient_range LB SP A n -> wr_at rsegs m' A n.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h01ih16__sat3h24__x1h34__x2h44__x3h51Hh62Hah77__arithh84__ffh96__sat2h:8__varmaph;5__with<1Ah=2H0h>2H1h?2HPh@2HRhA2HWhB2HihC2LBhD2SPhE1WhF2_HhG1ahH1mhI2m'hJ1np;1p;4p;2p;3p;7p;8g008Hj1KTg00R=j4hTg01B^j4@Tg00h6j22Tg00Ihj17Tg00JMj1LTg00Jkj2ZTg00ILj26Tg00M@j1FTg00M^j1TTg00NAj1RTg00Phj1PTg00?RR0j2;Tg011<j4CTg00Ncj1OTg00Z?j2\Tg00KHj2ATg00Zgj3[Tg00[Kj2YTg00Qcj2ITg00[lj1<Tg00\Kj29Tg00]4j3=Tg00]]j2HTg00^Ij1XTg00^ij3GTg00_Ij2JTg00_gj4WTg00`Ej1VTg00`cj1UTg015Fj2ETg00aNj2BTg00VJj1STg014cj3QTg01;aj3gTg00b1j2fTg00bSj2eTg00A@j3:Tg00c?j3cTg00c^j4bTg01<Dj7`Tg00?mj4MTg00Okj3_Tg00QJj1^Tg00hjj4NTg00iUj7aTg014?j7]Tg00j9j8dTg00SWR1f0R2'6p=1f2R3f1R4/A2';p=51242#Op=3f3R5g00TZR6?_34;:2#^p=0g00E]R7P4g00j]P2CNp=8P4g00kDR8g00kcR9P9g00lCR:P2g00lcFap=4P7P4g016MP2CNp=?P3P8P9P9P:P4P2F]p=DP5P8P9P9P:P3P4P2Gdp=>g002H#Kg00GKR8f5R;f4R<P5P3ChP6P<P3P4C@P0%151253g00T5R=#7R>#LR?%7>#7R@#7#7#7RA#LRB'ZRC'6%12RD?525%F@#TR@#RREf7RF13;4%P@R@C0[^07';f8RGPFP<P5CCP6f6RHP;P<C@[P2%1;12H;/6CA5D2HPEf:RI13G4P@C0[^07';P012FH/6CA5D2FPEf;RJf9RK/34P@C0[^07f<RLPJPGPFCCP6PIPKPGC@[P212KG/6CA5D2IPEf>RK13L4P@C0[^07f?R6PKPJPICC%1L12LJ/6CRJA5D2LRDPEP612K4RI#ORFP@C0[^07RM';PHPJPMP3PLPI1\?BRM1A1?RJ%1B1A1C[RN[RO%1?RPg00mCRQA[?B4UW6RB%1C\Q^6PRPP4g00m_1Y1?'IPJeO1RJPNg00nERQg00o1RR#<RS#<RT#<RU,97197T197RRR5=75=7g00oPRT'H%<U,97197S==7R5=7/HT%XQRT5GQ3G%KQRQP71J73P41J75CWRR%V7RS%U7RU1E71RV1B7>R>'8,4U%S=,B7RW,?>,4U5DURX%P9R9PU1B7=R==Q7WRW1E7?%FA5g7RA'8,4UP9PU18V=,4UP9AQ7=>R>,8V,4U1?>A,4U5DUC>C>C>1fU:R:P2P3g010<RAg010\RV'I1e23=:AVdAc714CbR1b8b:b;X27X37X47%14?543RV1245RA/6C%13125<R?#1?5?C[[[^27^37^47P2fAR?P;fBRCP<PGPLO6b7b1b9b1PCP?PKf=PIP3PMPOPBPPPJPNPTPQPRPSPUPXP918=>,4U1?>W,4U5DUC>P:P1b8b:b;X27X37X471243R1,64?51A\V^27^37^47P2P?P;PCP<O4b7b1b9b1F`O3P6PFO1f@RVPFO15:EPEPVPFP@C0PEPV1363R6P@C0[';P0PVP6O1P?P6O15:EPEP?P6P@C0PEP?13V5P@C0RV[PVP2PC13?<R?O1fCR<P?O15:EPEfDR?13C;P@C0PEP?13<HP@C0[P2PGPHP;O2O1WEWFP4P2O2n2001000000120000000bGXBDX07CMCMW@WAW>P4P2O2n2001000000121000000W5W=P4P2O2n2001000000121000000W5W?XJ7X<7XI8WHXD7WCo"). Qed.

Lemma rheap_pres_rw_cells : forall LB SP m m' A cs,
  rheap_pres LB SP m m' -> rw_cells rsegs m A cs -> rclient_range LB SP A (Z.of_nat (cells_size cs)) ->
  rw_cells rsegs m' A cs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h01Hh11Ah22HBh32HPh42HRh52HWh63Hwfh72LBh82SPh92csh:1mh;2m'h<1np;1p;4p;2p;6p;9g008Hj1;Tg00R=j4CTg01Cij45Tg01E8j49Tg01FHj11Tg019Wj10Tg01B^j43Tg011<j42Tg01GZj16Tg01Hjj17Tg017Qj44Tg00Ihj18Tg00M@j1<Tg00M^j1BTg018_j2ATg01J=j2@Tg00@Hj6?Tg01KWl9>Tg00?mj4:Tg01M:l9=Tg002H#;g00E]R0g00GKR1g01NZ#;f5R2f4R3f3R4f2R5CCg00TZR6P3P5f1R7C5g00?RR8P6P2P4P5C9P6P2P4%15#0C3f8R9f7R:P3%14#0C2P6f6R;P2P3C5[f0R<P6P:P2P3C9P8%62P6P9P;%72C4P6f9R2P:%1;#0C3f<R;f;R8P9%1:#0C2P6f:R3P2P9C5[[P<%6:P6P8P2%79C4P6P;P3%12#0C3f?R2f>R9P8%13#0C2P6f=R:P;P8C9P6P:P;%18R=#0R>C3%68P6P:P;%78R6C4P4f@R?P2P9P:P;P6P3P5g01A]R5P=fAP?P:%0<C2X<5P<g00T5#8#8#8#<#B/A61@84E?M9>C:P?P2P9P:P;P>P3P7P<M9=C:W4W5W2W6P7P<O2n2001000000120000000W0P7P<O2n2001000000120000000W0W3W9X10X;1W:W8W7o"). Qed.

Lemma rheap_pres_u8arr : forall LB SP m m' A xs,
  rheap_pres LB SP m m' -> u8arr rsegs m A xs -> rclient_range LB SP A (Z.of_nat (length xs)) ->
  u8arr rsegs m' A xs.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h01Ah11Hh22HPh32HRh42LBh52SPh61mh72m'h81nh92xsp;1p;4p;2p;3p;5p;6p;9g008Hj14Tg00Ihj11Tg00M@j16Tg00M^j15Tg00R=j4BTg01Ohj4;Tg018_j23Tg019Wj10Tg011<j42Tg01Q3j27Tg00^Ij18Tg00^ij39Tg01RAj5:Tg01SXj2ATg01T8j1@Tg00@Hj6?Tg01FHj1<Tg01T\l9=Tg01V?j6>Tg002H#4g00E]R0g00GKR1g00T5#1#1#1#6#5R2#4f5R3f4R4f3R5f2R6CBg00TZR7P4P6f1R8C;f7R9f6R:P51326#0C2P7P3P41325R2P5f8R;P9P:P3P4g01NZR<1725%8<39R<P6P7P:P4P5P8D:g01A]R8P2f9P;P3f0R3#0C2X88P3g00o1,A2%@2E?P;P9P4%<<#0C2eM9=E>W3W1W2W9X00X71W6W5W4o"). Qed.

Lemma rheap_pres_stk : forall LB SP m m' lo hi,
  rheap_pres LB SP m m' -> stk rsegs m lo hi -> SP <= lo -> stk rsegs m' lo hi.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "p'0h01bi001bh11ah26__sat3h34__x1h44__x2h54__x3h61Hh72Hah87__arithh94__ffh:4__p1h;6__sat2h<8__varmaph=5__with>1Eh?2H0h@2H1hA2HPhB2HShC2HWhD2HbhE2HihF2LBhG2SPhH2SThI1WhJ2W0hK2hihL1ihM2lohN1mhO2m'hP1oi011xp;1p;4p;2p;3p;6p;7p;8g008Hj1TTg00R=j4rTg01WVj4HTg00ILj25Tg00Ihj14Tg00JMj1ETg00Jkj2ZTg00KHj23Tg00M@j1NTg00M^j1UTg00NAR0j1qTg00Ncj11Tg00Phj1RTg01=fj2JTg00?RR1j29Tg00Z?j2]Tg00Zgj3\Tg00[Kj2[Tg00Qcj2PTg00[lj1CTg00\Kj2?Tg00]4j3@Tg00]]j2GTg00^Ij1YTg00^ij3KTg00_Ij2OTg00_gj4XTg00`Ej1WTg00`cj1VTg00aNj2ITg00VJj1:Tg00hjj4FTg015Fj2STg01;aj3pTg00b1j2oTg00bSj2nTg00A@j3<Tg00c?j3iTg00c^j4hTg00Voj1eTg00QJj1QTg00XLj2cTg00Yej2bTg012Yj6aTg00dPj3dTg00<ZR2j2BTg01>Hj2`Tg00@Hj6_Tg00@fj4gTg00?mj4LTg00Okj3^Tg01?oj3jTg00iUj7kTg014?j7lTg00j9j8mTg00SWR3f0R4'5p=;%44#4p=Df2R5f1R6'5/94p=6f3R7g00TZR8?^56;<4#Qp=0Aj856=<74p=21B64,95p=8g00E]R9P6g00j]P4CFp==P6g00kDR:g00kcR;P;g00lCR<P4g00lcFkp=7P5P:P;P;P<P6P4Flp=MP7P:P;P;P<P5P6P4Gmp=A1364,95p=f%44#4#4#4p=>g002H#Tg00GKR=f5R>f4R?P7P5CrP8P?P5P6CHf6R@/57P1%;?g00T5RA#4RB#ERC%DBRD#4#DRE#ERF'ZRG,57RH134?96>4%ND#URD#qRIf8RJ%16RK%RDRLC0PIf9RM%15RN1JD4ROC2X0D78D[^19'9P8P@P>P?CHP6%;@f7RP,3496J4PIf;RQPKPLC0PIf<RRPNPOC2X0D78D[^1996@GP115PG134J96M4PIPRPKPLC0PIf=RSPNPOC2X0D78D[^19P8f:RTPMPJCHP415MG134Q96R4PIf?RUPKPLC0PIf@RVPNPOC2X0D78DRW[^19%;R15QGRX134R96S4RYPW[^19RW'9P>PXPWP6PRP61]CFRW133CRX%;F133G[RZ[R[%;CR\g00mCR]A\CF6UW7RF%;G\]^7\R\P6g00m_1[3C'PPXeO1RXPZg00nER]g00o1R^#CR_#CR`#CRa,?91?9`R`1?9^R^5@95@9g00oPRb'G%Ca,?91?9_=@9^R^5@9/Gb%Y]R_5K]3K%T]RaP91O95P61O97CXRc%W9Rd%V9Re1I9BRf1I9ARg'=,7eP9Pgg016MRh%:ARA,I9RiCF,7e5Me%R;RjPe1S9C%NE5p9RE,=i,7ePjPe1S93RC/=f,7ePj1=Cg,7eP9PgPhPECF,7e5MeCACACA1oe<REP4P5g010<Rhg010\RC'P1n45=<hCdAi936ChR3b9b<b=X39X49X5913459664%;7RCAfC7G[\H[^39^49^59P4fARHfBRCP>P?PPPQO6b8b2b;b215H6%:B#:#D#:#4#>#>#>#E%:A#4#:#:#D#>#>#>#E,36766%e6#Q'91cC6'bPWP[PFP\PXPZp-0RZA@9`^/Gb=K]_PaPcPdPe1=if,7ePeP:P;P;P<P>Ea5MePjPe1=gi,7ePj1=gf,7eCACAPEP3b9b<b=X39X49X59W:A656715671557[[^39^49^59^:ZP413>HPCP>fERZP?f>R3O6b8b2b;b23dO3PUPKO1PVPKO15<IPIPVPKPLC0PIPVPNPLC0['9P1PVPNO1PHPNO15<IPIPHPNPLC0PIPH%17PLC0R7[PIPC%1?R?POC2X0D987DP4PCP?O1fCP?O15<IPIfDR?%1>PLC0PIP?%1@R?PLC0[PPP@P>O2PIPZP?PLC0PIfFR?%1PRPPOC2X0D78DP1PIP?PPPLC0PIfGRP%1JRJPOC2X0D,BDPIP?PJPLC0PIPP%1MRPPOC2X0D78DP4PIfHPPPLC0PIfJRP%1QPOC2X0D,BDP2PDPIfKR2%1RRRPOC2X0DPIPPPRPLC0PIP2%1SPOC2X0D78DP4PIfMRS%13POC2PIPS%1URUPLC0PIfNRL%1VRVPOC2X0DR3,BDPMP>O1PDP3P6PIPLPUO1P0PDPIP4PO1`8Vn101101000210100001JD55<IXPIP4PSPUO1PTE_PIPSPU1JD6C2eCgCLWDX0DP6P4O2n2001000000121101000W6WJP6P4O2n2001000000121000000b1WIW>P6P4O2n2001000000121000000b1XEYXL9CLCLWCW@P6P4O2n2001000000121000000W6W?P6P4O2n2001000000121000000WBWHWAXK9XM9XO=WNXG9WFo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rblock_range (A n : Z) : Prop :=
  0 < A /\ A mod 16 = 0 /\ 0 <= n /\ A + n <= alloc_ceiling /\ (A + n <= 0x10000 \/ 0xec000 <= A).

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition rclient_write_ok (LB : list block) (iv : Z * Z) : Prop :=
  alloc_ceiling <= fst iv
  \/ (0xb2000 <= fst iv /\ snd iv <= 0xec000 /\ (snd iv <= RLIBC \/ RCTX + 928 <= fst iv)
      /\ (snd iv <= RSSP_GUARD \/ RSSP_GUARD + 8 <= fst iv) /\ (snd iv <= RGOT_SSP \/ RGOT_SSP + 8 <= fst iv)
      /\ (snd iv <= RVMLOCKC \/ RVMLOCKC + 4 <= fst iv))
  \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition raddr_exposed (s : PState) (n : Z) : Prop :=
  MMAP_THRESHOLD <= n \/ ps_m s = ps_m (ps_init (reservedZ rsegs)).

Lemma raddr_exposed_big : forall s n, MMAP_THRESHOLD <= n -> raddr_exposed s n.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h01nh11sp;2p;1p;3g00ILj20Tg00=4j11Tg01Xaj13Tg01Z2j22Tg00A@j35Tg00dPj34Tg00F;g00E]g01[AR0f0R1'0f1,00g00C2f2#1p,4RUNpg00TZ#3'2#135;41UW0W1o"). Qed.
Lemma raddr_exposed_init : forall s n, ps_m s = ps_m (ps_init (reservedZ rsegs)) -> raddr_exposed s n.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h01nh11sp;1p;2p;3g00=4j10Tg01Xaj15Tg01Z2j22Tg00A@j31Tg00ILj24Tg00djj33Tg00F;g00E]g00C2R0f1R1#0p,4RUNpg00TZ#5'2#0R231g01[A/41f2#0=102f033UW0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rdeep_pres (lo : Z) (m m' : mem) : Prop :=
  forall a, alloc_ceiling <= a < lo -> m' (wa a) = m (wa a).

(* [comment removed for export] *)
Definition rimg_pres (m m' : mem) : Prop :=
  forall a, 0x10000 <= a < 0xec000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (RERRNO <= a < RERRNO + 4) -> m' (wa a) = m (wa a).

Definition rmalloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB (bv_unsigned sp) m m' /\ rdeep_pres lo m m' /\ rimg_pres m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m'
       | Some p => exists A junk,
           a0 = Z_to_bv 64 A /\ rblock_range A n
           /\ RHEAP s' ((p, A, n) :: LB) m'
           /\ rw_cells rsegs m' A [CB (Z.to_nat n) junk]
           /\ (raddr_exposed s n -> A = ptr_addr s' p)
       end.

Definition rmalloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^40 ->
  implM rsegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RMALLOC_SYM) fc None m (seg_rom rsegs)).

Definition rfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (lo B : Z) (errv : word) (m : mem)
    (r : unit) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]          (* [comment removed for export] *)
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m' /\ rdeep_pres lo m m' /\ rimg_pres m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ RHEAP s' (lb_remove p LB) m'.

Definition rfree_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  mem_inv rsegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM rsegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).

(* [comment removed for export] *)
Definition rfree_null_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  a0 = Z_to_bv 64 0 ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RFREE_SYM) fc None m (seg_rom rsegs)).

Lemma rfree_null_spec : rfree_null_stmt.
Proof.
ltac2:(KReplay.run1 (kr_t_RMalloc_iface ()) ["CEIL_WRAP_1"] "h01bh13ms'h21Hh36HPsteph45Psteph56R0steph62a0h71zh81Fh92a1h:2a2h;2a3h<2a4h=2a5h>2a6h?2a7h@2fchA2gphB1mhC2rahD2s0hE2s1hF3s10hG3s11hH2s2hI2s3hJ2s4hK2s5hL2s6hM2s7hN2s8hO2s9hP2sphQ2t0hR2t1hS2t2hT2t3hU2t4hV2t5hW2t6hX2tpp%0p;1p;2p;3p;Op;7p;6p;4p;Bg00Ihj14Tg00M@j1ETg00M^j1YTg00VJj1:Tg01\Yj2mTg01]Ej28Tg00A@j39Tg01]klODTg01_6j1ITg00Phj1^Tg01>Hj1]Tg01`Ej7=Tg00JMj15Tg01aPj2dTg00NAj1ZTg01=fj20Tg00Qcj2?Tg01b<j2STg01c>j1RTg01d>j2`Tg01d^j1OTg01eOj1_Tg01fWj2MTg01g?j2HTg00h6j2CTg01hIj2GTg01i3j2XTg00@Hj6<Tg01jNj3LTg01k9j3JTg01k^j3TTg01lkj4qTg01mWj1pTg01nDj42Tg01o1j3WTg01o^j2oTg0212j2\Tg01?Sj6[Tg021Oj4lTg021kj3iTg022Wj1hTg023Dj2UTg023ij3FTg024Nj1fTg025bj1eTg0279j1cTg027Zj4gTg028ilBVTg02:?j3bTg02;Ij2jTg02<<j3kTg02<_j4aTg02=?j2nTf0R0#4#4p=1g00TZR1f1R2;b0p=B%:0#:p=@%40#:p=A%:0#4p=;f3R3f2R41j203kp=>g010<R5g02>GR6790p=Qg02>gR7g00E]R8P2P0Cap=Pg02?SR9f6R:f5R;f4R<P3P4P2P0F='np=7P:P;P<P3P4C2P2P0C2p=6P<P31042P0C2p=3P:P;P<P3P4P2P0C2C2p=Kg010\R=9950p=Ng00T5R>#4R?#4R@#1RA#4RB#4S00#ERC#YRD%:?R?#ERE/mDRF%EBRB#YRGg00GKfHRHg00SWRI,8CRJ59DPDPJfTRKfSRLfRRMfQRNfPROfORPfNRQfMRRfLRSP2fJRTfIRUPHfGRVfFRWfERXfDRYfCRZfBR[fAR\f@R]f?R^f>R_f=R`f<Raf;Rbf:Rcf9Rdf8Ref7RfP:MODP;%IKS01P<%^DRgP3%]1RhF=9990X19PLPMPNPOPPPQPRPSfKRiP0PUPHPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfP:P;MODP<g02@Z,8CS02P3PgP4PhF='BX6DP1PLPMPNPOPPPQPRPSPiPJPUPHPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfP:P;MODRjP<%ILS03P3PgP4PhF=S049990X19RkPMPNPOPPPQPRPSPiPTPJPHPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfP:P;P<MODS05P3%:@#@Rl#A#@#1#;#A#@#1#5Rm,8CRnP4PgP2PhPB%;A#A#1RA#4#1#1#1#1#1#1Ro#:#;#@#@#5RpPBPpC>RpPEPIPE%5oC>%4?R?#:#ERo%5ARAPoPAC>RA'dRq%5@R@Q05P3%;l#1Rl#4#A#;#1Rr#4#1#5Rs,8CRtP4PgP2PhF=S06%ZGRu10GpRv'?1S1n=9uvd1?56S07%Rp#Qd1`78R7#ZR61Pq@,07Rq'?%Op=96qd%_9p-0[RqP0PjP<PtP3PgP4PhF7O1PKPLPMPNPOPPPQPRPSPJPTPUPHPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfP:MODS08PFPD1MoARj,HnRpP3P2PfP0P:PgP;PhF7O1X0DRvPD1Cmj,8CPvP21GCn/Cj,8C1XmjE<P4P0P:PpP;PgP<PhF7O1eALoCA9JCnATnoAE<b5W3W4P1PkQ05P3PtP4PgP2PhPB%:>RA#:#1Ro#1#1Rn#4#;#;Rp#4#1#A#1#A#;#1#@#5RjPBPjC>Rjg02B3PE%5?PE%5pC>PEPIPE%5nC>%4AS09#:#ERA%;o#1#5RoPAPoC>RoCqRnP@PDPDPDPDPDPD%pDRp10D<Pp10DYS0:PpF610DSS0;PDPpPDPaPpD3S0<10DORSPDPDPpPDP]PpD3S0=10DHS0>PDPpPDPePpD3S0?C2S0@F610DMR?PDPDPDPpPDP[PpD3S0APDPTPDPpPDPcPpD3S0BD3S0C10DQRmPDPDPpPDP_PpD3S0D10DWS0EPDPpPDP:PpD3S0FC2S0GC2PgPDPDPDPDPpPDPZPpD3S0HPDPiPDPpPDPbPpD3S0ID3S0J10DPRvPDPDPpPDP^PpD3S0K10DVS0LPDPpPDPfPpD3S0MC2S0NC2S0O10DNRwPDPDPDPpPDP\PpD3S0P10DJRxPDPpPDPdPpD3RyC210DRS0QPDPDPpPDP`PpD3Rz10DXR{PDPpPDP;PpD3R|C2FKF6P3P5PDAWCJJR}%;l#;#1#;#1#5,8CRl%:r#1#5,8CS0Rn0100000020000RrP4PgP2PhF=S0S10GjR~,?u1S1t=9u~dQ07%Rj#Qd1Pn@,07Rn,?6%Oj=96ndP0PDPDPDPDPDP|P{PpC2Q0QPzPwPDQ0PPDPUPyD3S0PF610DLRyQ0OPgPDPDPDPDPpQ0:PpC2S0:Q0;Q0<C2R|PSQ0@C2S0;P?PDPDQ0APxQ0BC2PmQ0GFKF6RnP<PrP3PgP4PhF7O1Q08PFPD1MAoRF,HtRrP3PDPDPDPDPDQ0?Q0>PpC2PSQ0=10DKS0=P|F6fVR|,0DPDPDPDPpQ0EPpC2PmQ0DP?Q0CF6S0>PgPDPDPDPDPpQ0LPpPvQ0KF6PyQ0JfURj,0DS0?PDPDPDPpP{PpC2S0GPxPzPwQ0PF6F6F6R{PfP5PDg02BeS0B9WCJS0AP018C@9JCtS0On0100000020000P:PgP;PhF7O1X0DPD1Cs@,8CR~P3P{PfP5PDQ0APrP0n0100000020000P:PgP;PhF7O1X0DPDPJP3P{PfP5PDAWCJ0PrP~n0100000020000P:PgP;PhF7O1X0DPD1CsF,8CP3P{PfP5PDP}P0P~n0100000020000P:PgP;PhF7O1X0DP21GCt/CF,8C1XsFE<P4PDPDPDPDPDQ0MQ0LPpC2PvQ0KPyQ0JF6Q0?PDPDQ0GQ0QPzPwQ0PF6RwPgPDQ0>Q0=PDPDQ0:PxQ0<C2PSQ0@FKF6RSP:P5PDP}PrP~n0100000020000P;PgP<PhF7O1eQ0Bg02CJE<Q0O1os@E<ALACo9JCtATtAoE<b5W3X4qP5P}P=1?8I1GCJRo998IRAdPAP8PI1\00#NX781?5=PoP0E[b21\oo#Ne%N}eClA95=}P5P=PjPKPLPMPNPOPPPQPRPJPiPTPUPHPVPWPXPYPZP[P\P]P^P_P`PaPbPcPdPePfMODP:%IjP;PgP<PhF=9990X19PDPDPDPDPDQ0FQ0EPpC2PmQ0DP?Q0CF6Q0=Q0;PgPDPwPyPDPDQ0HPxQ0IC2PvQ0NFKF6RvP;P5PDP0PlQ0Rn0100000020000P<PgP3PhF='BX05P1Q08P;Q01P<PgP3PhF=9990X19R5PnP<PlP3PgP4PhPBQ00#1Rx#:#;#A#@#5RyPBPyC>RyPEPIPE%5xC>PE%5>R>PEP>C>Q09#4#EREPIPEPIC>Rx3iRBP@PnP<Q03P3PgP4PhF=Rw10GyRG,?u1S1l=9uGdQ07%Ry#Qd1PB@,07R7,?6%Oy=967dP0PvP;Q01P<PgP3PhF7O1PS%hDPD1MExRS,H|RvP3P2Peg02DYR7,UC9FC0PfPgP:PhF7O1X0DPD18C>R>P3P2PefW/HS1UC05FCPfPgP:PhF7O1X0DP81GC|RSP3P2Pe18C01UC>R>5FCPfPgP:PhF7O1X78PDP|P3P2PeAFC0>PfPgP:PhF7O1X0DPD%I|P3P2PeP0PfPgP:PhF7O1X0DP2AFC|>%f|E<18CS%e|E<1CSI%cSE<P4P0PfAFCv>P:PgP;PhF7O1eP7g02E>E<ALECx9JC|AT|ExE<b5W3X4qP1P5PwQ04,?9Cg1B5weMBVPnP<PlP3PgP4PhF=,B5eP}P0E[b2Q0S,BkeMBVQ06,BkeMBVQ05P3Q02P4PgP2PhF=,BkePUP0E<W2WBW@W8XWDXVDXUDXTDXGDXFDXODXNDXMDXLDXKDXJDXIDXHDX?DX>DX=DX<DX;DX:DX9DX6DXEDXDDXSDXRDXQDXXDXADXPDWCg02FMeo"). Qed.
End CEIL_WRAP_1.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
