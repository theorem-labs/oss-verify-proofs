(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FuzzProducer HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AHarness_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AH_huf_iface AF_huf_dec_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_z4m () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Arr4u64sI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftrK47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes8list_indC47Corelib5Lists7ListDef3mapI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3mulK47Corelib4Init9Datatypes3nat02C47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib5Arith8PeanoNat3Nat3mulC56Stdlib6ZArith4Znat5Nat2Z7inj_mulC56Stdlib6ZArith4Znat5Nat2Z8inj_succC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfK47Corelib4Init5Logic3and01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m>z4_cells_wf_C8c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4mAz4_cells_bytes_C8c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m@z4_cells_size_C8C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsI47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waK47Corelib4Init9Datatypes6option02C47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr07K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl4aptrC46Stdlib5Lists4List2hdC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_layoutC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_botC5ARocqVerifyHarness?AgentSubmission5BothW5ABase6al_topC56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl;a_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase<al_space_begC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Peano2le00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7al_fakeK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission3Lib8RunConst:ATOP_rangeC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission5BothW5ABase5AUMAXC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MINC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst8ATOP_MAXI47Corelib4Init9Datatypes:comparison00K46Stdlib9micromega:ZMicromega;ZArithProof01c5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m3Z4MC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m4Z4F0I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame?stk_of_rw_cellsc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m?z4_C8_of_u64arrC47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_mergec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m<z4_sp_boundsC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface3aciC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface=aclient_rangeC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_ifaceAaclient_app_rangeC46Stdlib5Lists4List2InC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_addrC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7ab_sizeI47Corelib4Init5Logic2or00K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind02K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock01K47Corelib4Init5Logic2or01K5ARocqVerifyHarness?AgentSubmission5BothW5ABase6abkind01K47Corelib4Init5Logic2ex01K47Corelib4Init5Logic2or02K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface8AI_frameC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI5ARocqVerifyHarness?AgentSubmission5BothW5ABase6ablock00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed6ASHOFFC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface<aclient_addrC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission5BothW5ABase9in_rangesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8in_blockC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7in_fakeC5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface:AI_aci_imgC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface?AI_block_boundsC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface9AI_aci_loC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1Z4of_NC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission6Common8DrvAgree6magreeI47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC5ARocqVerifyHarness?AgentSubmission5BothW<AH_huf_iface=huf_dec_postAC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF6acc_inC5ARocqVerifyHarness?AgentSubmission4LibA5StepF=rng_acc_litZ'C5ARocqVerifyHarness?AgentSubmission3Lib4Step@rw_cells_read_atK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib4Step@Z_to_bv_lit_selfC56Stdlib6ZArith6BinInt1Z7add_0_rC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC5ARocqVerifyHarness?AgentSubmission3Lib6MState6ret_pcK4ELinuxProcessSemantics5Riscv5Instr5instr04C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC5ARocqVerifyHarness?AgentSubmission3Lib6MState;ret_pc_foldC5ARocqVerifyHarness?AgentSubmission5BothW=AMalloc_iface5AHEAPc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m9z4_magreec5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m8z4_aheapC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9evtF_doneC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF4evtFC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr06K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5StepF<lift_resultFK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C5ARocqVerifyHarness?AgentSubmission3Lib4Step=wa_of_Z_to_bvC47Corelib4Init5Logic6eq_symC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission4LibA5StepF9stepF_genC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=step_accessesC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF=evtF_step_accK4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w1C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w1_litc5ARocqVerifyHarness?AgentSubmission5BothW:AF_huf_z4m7AZ4_EPI".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AZ4_SLOW : Z := 0x87d04.     (* [comment removed for export] *)
Definition AZ4_EPI : Z := 0x8776c.      (* [comment removed for export] *)
Definition AZ4_M10 : Z := 14757395258967641293.   (* [comment removed for export] *)
Definition AZ4_M7 : Z := 2635249153387078803.     (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma z4_cells_bytes_C8 : forall ws, cells_bytes (map C8 ws) = u64s ws.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4m ()) [] "h02wsh12IHh21lh31wp;1p;3p;2p;6p;5p;4p10000p4p7210g000\R0p4p710p8g001:j14Tg001_j1?Tg002=j1>Tg002`j1:Tg003@j18Tg004:j15Tg004kj37Tg005Ej1=Tg005ej2<Tg006?j2;Tg006ij21Tg007Oj1@Tg007mj20TP0j6CTg008Mj36Tg008mj5BTg009Oj4ATf1R0g009kg00:`f0R1CAp=9f4f3R2f2R3?60136p=31130=621p=2g00;U#4#4#4R4#4#4#4#?R5#>R6#:R7P6%?4R8#>R9#:R:1961#8%5137R;X07%=9,<:%=6R<,96#8%5<57:eP:%50R<P91;52R2,18R=P9%@4R4,02R2,18R>P91024R2,18R?P91024R2,18R@P91024R2,18RAP91024R2,18RBP91024R2,18RCP91024,18R2P1D3D3D3D3P9P=P9P>P9P?P9P@P9PAP9PBP9PCP9P2%53D3D3D3D357:X2:P9P81;53R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054R5P9P81054P<C2C2C2C2C2C2C2C2,<:1960#8P1ECA6630R3,96#8%5357:eX1;X07X36P1DBW0o"). Qed.
Lemma z4_cells_size_C8 : forall ws, cells_size (map C8 ws) = (8 * length ws)%nat.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4m ()) [] "h02wsh14__x1h21xh32IHh43IH0h57__arithh64__ffh78__varmaph85__with94cstrh:5cstr0h;1nh<1wh=1yp;1p;2p;3p;4p;7p;6p;5p;Bp;<g001:j1>Tg001_j1eTg002=j1XTg002`j1ETg00<:j1@Tg00=3j28Tg00=Sj2ATg005ej2<Tg005Ej1GTg00=jR0j11Tg00>Ij25Tg007Oj1JTg00>`R1j19Tg00?@R2j2KTg00?]R3j20Tg004kj3=j1ITg00@:j2YTg00@]j3WTg00A:j4STg00Aaj1FTg00BFj2DTg00Bbj2QTg00C@j1PTg00C^j1OTg00DIj2BTg00Dlj2NTg00EOj3RTg00F2j4MTg00F]j7TTg00GAj2dTg00Gcj2cTg00HOj3bTg00Hnj4aTg00I`j4`Tg000\j6_Tg008Mj3^Tg008mj5]Tg009Oj4\Tg00JKlBCTg00K1l<[Tg00KVl<ZTg00L;j3LTf1R4g009kg00:`f0R5C\p=?%15#1p=6g00L^R6?=45p=;1545#1p=7P6P6P6g00M=R7P7P7g00M[P1P1P1P2g00N;f5R2f4R8f3R9f2R:P4P5MBCp=VP6P6P7P7P0P1P1P9g00N^P:P4P5M<[p=2P6P6P6P7P7P7g00OBR0P1P1P1P3g00ObR;P9P:P4g00PER<g00PdR=P5MBCp=UP6P6P6P7P7P7P0P1P1P1P3P;P2P8P9P:P4P5MBCp=:P6P7P5P1P4P:P9P8P2f6f7f8M<Zp=HAL7:4=L75p=310:4/05p=4g00;UR8#>#>#>R1#>#>#>#e#XR;#ER3P;1?;5#@%6<#6#6#6R018;5'A';R>X031<6<%G;R?,?;#@18;?,A0';eP618;4R?,A0R@%65#6#6#618;:RA17A<,7A,7A,7A,7A,7A,7A'7';X;6%1@RA#1RB#1RC#1RD#1RE#1RF#1RG#1RH15?<R<#1RI,5?RJ#1RK,5?RL#1RM,5?RN#1RO,5?RP#1RQ,5?RR#1RS,5?RT#1RU,5?RV#1RW';%J1R1%9?RX'KRY%J8RZ'0R[/0ZR\/0ZR]/0ZR^/0ZR_/0ZR`/0ZRa/0ZRb10X=Rc/0ZRd,0XRe/0ZRf,0XRg/0ZRh,0XRi/0ZRj,0XRk/0ZRl,0XRm/0ZRn,0XRo/0ZRp,0XRq/0ZRr5=7%I6Rs%I7Rt%94%955=71;451Y453WX=6X26R6PHPb105ZX27RbPGPaPbPFP`PbPEP_PbPDP^PbPCP]PbPBP\PbPAP[PbP@PYP0P11<71P?PX1<7XR[EVRAC2C2C2C2C2C2C2C2PWPrPbPVPqP?PXP[PUPpPbPTPoP?PXP[PSPnPbPRPmP?PXP[PQPlPbPPPkP?PXP[POPjPbPNPiP?PXP[PMPhPbPLPgP?PXP[PKPfPbPJPeP?PXP[PIPdPbP<PcP?PXP[1<7=CUC2E:C2E:C2E:C2E:C2E:C2E:C2E:C2M9H1?;4#@R[/;@%9[RX==7YR?PsPtP6P[PX1<7XP@PYPAM9HP5CSP?1?;:#@R?#F%9?,D=18;9R9#F%99,D=g00QBR9#G%E91Q74%P7%O7R9g00Qng00RMR?P?g00RmR?P71B711N78R85R71B7ZRA;3A?3AA?3AA?3AAg00SM1B7==38A=38A=38A=38A=38A=38A=38A=38ACMg00T4FT1d9?P5P:g00TTR?g00U4R9'<1c5:==?9dAb7=4Cab6b7b8X171K15?4ZZ?4ZZ?4ZZ?4ZZA45=Z=45Z=45Z=45Z=45Z=45Z=45Z=45Z5=7^17P518;2#9O1b5b:b9b4C`P[P5E_A^;:4R:,?;#@18;:,A0';eX3>X03X<;P5D]W0o"). Qed.
Lemma z4_cells_wf_C8 : forall ws, cells_wf (map C8 ws).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4m ()) [] "h02wsh12IHh21wp;1p;4p;3p;5g001:j10Tg001_j1:Tg002=j14Tg002`j13Tg00UTj11Tg005Ej19Tg00VKj45Tg008Mj36Tg008mj57Tg009Oj48Tf1R0g009kg00:`f0R1C8p=2g00;U#0#0#0#0#0#0#:#4R2#3R3P21221#1R4X03g00VfR5%92,22#1eg00WB1220#1P5P1C5f2=620,22#1eX14X03X22P1D7W0o"). Qed.
Lemma z4_C8_of_u64arr : forall m A ws, u64arr bsegs m A ws -> rw_cells bsegs m A (map C8 ws).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4m ()) [] "h01Ah11Hh22Hbh32Hwh41lh51mh61nh72wsh81zp;1p;4p;2p;6g001:j12Tg001_j19Tg002=j1:Tg00W^j1>Tg002`j1<Tg00X@j4HTg004:j17Tg00Y3j44Tg007Oj1?Tg00=3j25Tg00>`j11Tg00?@j26Tg00Yhj43Tg009Oj4=Tg00ZZj4JTg00[Pj4ITg00<:j1GTg00UTj1DTg003@j1CTg00\Gj1BTg00]Kj1ATg000\j68Tg00VKj4;Tg00=jj10Tg00=Sj2@Tg00N;j2ETg00^Rj1FTg00;U#2#2#2R0#2#2#2#9#:R1%90#:R2#>[g00M=R3%<1g00_XR4f2R5f1R6f0R7CHg00`MP4f3R8P5%76C4P4P8P5%?0R01516#1'6C3P4f4R9P8P1g009kR:g00:`R;P5C=CJP7P4f5R5P9%78C4P4f6R8P51519#1,60C3P4f7R0P8P1P:P;P5C=R;CIP4P0P8%G;R:#1C3%D;P4P0P8%C;R;C4%B5%<2R2%75P4f8R8P0P7C4X42P6P;%A5E8C;g00L^R;g00PE#0#0#0#0#0#0#0#0R21515R1'@R9P4P8P0%17C3X6;P3%12%11'6P4P8P0P7C3X83P7%191E21E8P:%F5E8C;W3W2P6P7O2n2001000000121000000W1W7W0W5o"). Qed.

Lemma z4_stk_of_wr : forall m A n, stk bsegs m A (A + n) -> wr_at bsegs m A n.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_z4m ()) [] "h04__x1h11bh24__x2h31ah42H0h57__arithh64__ffh78__varmaph85__with94__x3h:1ih;1Ah<1Hh=2H1h>2H2h?2Hih@1mhA1np;1p;2p;4p;3p;7p;8g001:j19Tg001_j1LTg002=j1CTg00W^j1STg00?]j20Tg00`hj4ZTg00BFj22Tg007Oj1DTg00aZj2VTg00b7j26Tg00bSj1:Tg00cBj1KTg004kj31Tg00cdj17Tg00d=j3<Tg00dmj2YTg00eOj2;Tg00`MR0j24Tg00Yhj4FTg005Ej1XTg002`j1WTg00Bbj2@Tg00C@j1UTg00C^j1TTg00DIj2HTg00Dlj2?Tg00GAj2RTg005ej2QTg00Gcj2NTg00HOj3OTg00Hnj4PTg00eij1MTg00fGj4GTg00L;j3BTg00fej3`Tg00gHj1_Tg00F2j4ATg00VKj4ITg00gmj3^Tg00F]j7]Tg00hjj8\Tg00iNj7[Tf2R1f1R2'2f0R3'4p=3g00_XR4?^23p=51623,41p=Eg00M=R5P2g00j2P3CAp==P2g00QnR6g00RMR7P7g00RmR8P3g00T4F]p=8f3R9P6P7P7P8P1P2P3G\p=>P1P6P7P7P8P2P3F[p=Jg00;UR6#9R:#9#9R;#9#9#9R<#LR=#C%L;#CR;#SR>[P4P1P21023CZP0g00PdR?/211012%D:R@%D<'VR<1091,639393f5RA%:2RB'5%K;RC51>#7f6RD%:1RE5<41Y;3RF51>X1;,;;'4[^3533P4f4RGP9P1CFP312?G10AG10DARA,6393D3f8RG/5B=1>C#7f9RH=<4E=1>FX1;,;;'4[^3573<P012A<f7RA10AD,6373315HB=1>C#7f:RI=<4E=1>FX1;,;;'4[^35P4PGPAPDCFP310GA/2<10IHRH,6393I3f<RA/5B=1>C#7f=RB=<4E=1>FX1;,;;'4[^3512?I12H<RH12?3RE?E3IRG10A2RJ#:,5B=1>C#7[^:5RK'4g00QBRL#XRM%WLRL1@52%U5RN%T5RO1H5?RP1?56RQ'=,8ORR%K7R7PRC>1RO8R8P3P1g00TTRRg00U4RS'Q1N31=1RSdAO5?2CPRSb6b7b8X0512?2R?\E^05P3f;REPDO2b5PHPKPMPLP51@51RKP2%M5CGPNPO1?5:R:9B5QRH1H5@=`5='=,8OR=P7P=C>P8PSb6b7b8X05X251032/2<1021R=/2<[^05^25P3PIPEP1O3b510AE,6J93AJRJP0f>R010B1RA#:'5=1>C#7REf?RI1009#:R<5<4=1>FX1;,;;15I<=1>C#7P9PAP3O2P2n2001000000120000000UPE\JP3PMPLP5PKP21@59CGPNPO1=P:,8OP5P:g00jYR:%_6,?5R6CA,8O5JOP71=QH,8OP5PHP:AB5Q6CA,8O5JOC>P8PSb6b7b8X05X25X95AE?211029,6=932=[^05^25^95P3PBP9P0P1O4b5O1b4X?GX:5CICIW<W>P2P3O2n2001000000121000000W4W=P2P3O2n2001000000121000000W4XA5X;5W@o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Z4.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).
  Variables (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32) (m0 : amem).
  Variables (DST dcap SS DT mtl lo : Z) (src : list Z) (cbs : list byte) (pdt pb : aptr).
  Notation SP := (bv_unsigned sp).
  Notation SPF := (SP + -528).
  Notation n := (zlen src).
  Notation seg := ((dcap + 3) / 4).
  Notation DTL := (DTABLE_BYTES mtl).
  Hypothesis AH : AHEAP AI L RNG st LB m0.
  Hypothesis HDT : In (HB pdt DT DTL) LB.
  Hypothesis HDB : In (HB pb DST dcap) LB.
  Hypothesis LOA : ATOP + 4096 <= lo.
  Hypothesis LOS : lo <= SP - HUF_DEC_STACK_A.
  Hypothesis SPT : SP + 16 < al_top L.
  Hypothesis SP16 : SP mod 16 = 0.

  Notation DW := [(lo, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_postA AI L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma z4_sp_bounds : 0x10007fff8000 <= SPF /\ SP <= 2^47 /\ ATOP + 4096 <= lo /\ lo + 8192 <= SP.
Proof using AH LOA LOS SPT.
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
  unfold HUF_DEC_STACK_A in LOS. lia.
Qed.

  (* [comment removed for export] *)
  Definition Z4F0 : list cell :=
    [C8 (Z_to_bv 64 SS); C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 dcap);
     C8 (Z_to_bv 64 (DST + dcap))].

  Definition Z4M (mm : amem) (w136 : word) (ws : list word) : Prop :=
    (exists buf, u8arr bsegs mm DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap)
    /\ bytes_at bsegs mm SS (map (Z_to_bv 8) src)
    /\ bytes_at bsegs mm (DT + 4) cbs
    /\ stk bsegs mm lo (SPF + 24)
    /\ rw_cells bsegs mm (SPF + 24) Z4F0
    /\ stk bsegs mm (SPF + 72) (SPF + 128)
    /\ rw_cells bsegs mm (SPF + 128) [C8 (Z_to_bv 64 (DT + 4)); C8 w136]
    /\ u64arr bsegs mm (SPF + 144) ws /\ length ws = 19%nat
    /\ stk bsegs mm (SPF + 296) (SP + -104)
    /\ rw_cells bsegs mm (SP + -104) FRS
    /\ mem_inv bsegs mm /\ munch DW m0 mm /\ wmono bsegs m0 mm.

  (* [comment removed for export] *)
  Lemma z4m_stk : forall mm w136 ws, Z4M mm w136 ws -> stk bsegs mm lo (SP + -104).
Proof using AH LOA LOS SPT.
  intros mm w136 ws (_ & _ & _ & S0 & F0 & S1 & F1 & AR & LW & S2 & _).
  pose proof z4_sp_bounds as SPB.
  pose proof (stk_release bsegs mm lo _ _ S0 F0 ltac:(lia)) as L0. unfold Z4F0 in L0. cbn [cells_size csize Nat.add] in L0.
  replace (SPF + 24 + Z.of_nat 48) with (SPF + 72) in L0 by lia.
  pose proof (stk_merge bsegs mm lo (SPF + 72) (SPF + 128) L0 S1 ltac:(lia)) as L1.
  pose proof (stk_release bsegs mm lo _ _ L1 F1 ltac:(lia)) as L2. cbn [cells_size csize Nat.add] in L2.
  replace (SPF + 128 + Z.of_nat 16) with (SPF + 144) in L2 by lia.
  apply z4_C8_of_u64arr in AR.
  pose proof (stk_release bsegs mm lo _ _ L2 AR ltac:(lia)) as L3. rewrite z4_cells_size_C8, LW in L3.
  replace (SPF + 144 + Z.of_nat (8 * 19)) with (SPF + 296) in L3 by lia.
  exact (stk_merge bsegs mm lo (SPF + 296) (SP + -104) L3 S2 ltac:(lia)).
Qed.

  (* [comment removed for export] *)
  Lemma z4_aheap : forall mm, munch DW m0 mm -> wmono bsegs m0 mm -> AHEAP AI L RNG st LB mm.
Proof using AH HDB LOA LOS SPT.
  intros mm MU WM. pose proof (AI_layout AI L RNG st LB m0 AH) as HL. unfold HUF_DEC_STACK_A in LOS.
  eapply (AI_frame AI); [exact AH | exact MU | exact WM |].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd]; unfold aclient_range, aclient_app_range.
  - left. left. lia.
  - right. left. exists (HB pb DST dcap). split; [exact HDB|]. cbn. lia.
Qed.

  Lemma z4_magree : forall mm, munch DW m0 mm -> wmono bsegs m0 mm ->
    magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ (DST <= a < DST + dcap)) m0 mm.
Proof using AH HDB HDT LOA LOS SPT.
  intros mm MU WM. apply (munch_magreeA DW m0 mm); [exact MU | exact WM |].
  intros a [CA ND]. cbn [outside]. split; [| split; [exact ND | exact I]].
  pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
  destruct CA as [S | [R | [B | (a' & A' & E)]]].
  - lia.
  - destruct R as (iv & IN & R1 & R2). pose proof (AI_aci_img AI iv IN) as HI. unfold ABase.AIMG_HI in HI. lia.
  - destruct B as (b & IN & B1 & B2). pose proof (AI_block_bounds AI _ _ _ _ _ b AH IN) as (BB1 & BB2 & BB3).
    unfold ABase.AIMG_HI in BB1. lia.
  - subst a. unfold shad, ASHOFF. rewrite ?Z.shiftr_div_pow2 by lia.
    assert (A'B : 0 <= a' < 2^47).
    { destruct A' as [A1 | [(iv & IN & R1 & R2) | (cls & A & k & IN & F1 & F2)]].
      - lia.
      - pose proof (AI_aci_img AI iv IN). pose proof (AI_aci_lo AI iv IN). unfold ABase.AIMG_HI in *. lia.
      - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH IN) as (BB1 & BB2 & BB3). cbn [ab_addr ab_size] in BB1, BB2, BB3.
        unfold ABase.AIMG_HI in *. lia. }
    Z.div_mod_to_equations. lia.
Qed.

  (* [comment removed for export] *)
  Lemma z4_epi : forall mm (t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra : word),
    stk bsegs mm lo (SP + -104) -> rw_cells bsegs mm (SP + -104) FRS ->
    mem_inv bsegs mm -> munch DW m0 mm -> wmono bsegs m0 mm ->
    rng RNG lo (al_top L - lo) ->
    evtF bsegs RNG POST (MS (mkR xra (Z_to_bv 64 (SP + -528)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                                 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6) FR (Z_to_bv 64 AZ4_EPI) fc None mm (seg_rom bsegs)).
Proof using AH HDB HDT LOA LOS SPT.
  intros mm t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 xra ST FRB MI MU WM RL.
  pose proof z4_sp_bounds as SPB. pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & _).
  unfold AZ4_EPI.
  do 13 zstep. zstep. zstep.
  release_frame FRB ST (bv_unsigned sp).
  apply evtF_done. unfold huf_dec_postA.
  try (lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned sp + ?k + ?k')] =>
         replace (bv_unsigned sp + k + k') with (bv_unsigned sp) by lia end).
  rewrite ?Z_to_bv_bv_unsigned.
  do 16 eexists. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST|]. split; [apply z4_magree; assumption | apply z4_aheap; assumption].
Qed.

End Z4.
End CANSEC1.
