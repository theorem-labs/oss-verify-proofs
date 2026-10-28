(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_rs_pure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_rs_cl () := "C46Stdlib5Lists4List=nth_error_mapC47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC47Corelib4Init9Datatypes:option_mapC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C47Corelib5Lists7ListDef3nthK47Corelib4Init5Logic2eq01C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC46Stdlib5Lists4List>nth_error_nth'C47Corelib5Lists7ListDef3mapC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib5Lists7ListDef6Forall01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic7f_equalK47Corelib5Lists7ListDef6Forall02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7upd_natC47Corelib4Init9Datatypes8list_indI47Corelib5Lists7ListDef6Forall00I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6shiftlC45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallK47Corelib7Numbers7BinNums1Z03C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC56Stdlib6ZArith6BinInt1Z:shiftl_1_lC56Stdlib6ZArith6BinInt1Z3subc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl5cl_okc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl6cl_invI47Corelib4Init9Datatypes4prod00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K47Corelib4Init9Datatypes4prod01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C47Corelib4Init5Logic8iff_reflC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3u32C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure<collect_stepC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setK4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude4zextK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3ltbK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas8zload_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas9zstore_okK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2wac5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl<nth_map_ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u32arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4K4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u32arr_store_okC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics5Riscv3Sem4core01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega=RingMicromega5Psatz07C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;map_upd_natC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5shl32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliK4ELinuxProcessSemantics5Riscv5Instr5instr0=C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_sllwC4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_sllwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addwC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6w_addwC56Stdlib6ZArith6BinInt1Z9add_assocC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes4andbC46Stdlib4Bool4Bool=andb_true_iffC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega5Tauto8GFormula01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03C35stdpp7tactics<f_equal_helpC46Stdlib5Lists4List;Forall_implc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl>Forall_upd_natC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas>upd_nat_lengthC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats<collect_loopC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure;collect_endC46Stdlib9micromega;ZifyClasses7rew_iffc5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl5cl_pwC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zr_mod_anyC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge9zr_shiftrC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge:zb_shl_shrC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit>unsigned_byte'C5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit2:sx32_smallC47Corelib4Init9Datatypes7nat_indC47Corelib5Lists7ListDef5skipnC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics5Riscv3Sem5alu64C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega5Tauto8GFormula0:C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsC5ARocqVerifyHarness?AgentSubmission4Spec@HufPure_HufStats@HUF_TABLELOG_MAXC56Stdlib6ZArith4Znat5Nat2Z8inj_succI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00I4ELinuxProcessSemantics5Riscv3Sem4core00K46Stdlib9micromega5Tauto4kind02C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedK4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05K4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr5aluop07".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma nth_map_Znth : forall (l : list Z) i, 0 <= i < zlen l ->
  nth_error (map (Z_to_bv 64) l) (Z.to_nat i) = Some (Z_to_bv 64 (Znth i l)).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_cl ()) [] "h04__p1h14__p2h24__x1h34__x2h44__x3h51oh61xh71Hh82H0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1ih?1lh@2z0p;1p;2p;3p;4p;7p;5p;6p;<p;8g0000R0p4p7210g000RR1p4p710p8g0010j1MTg001Pj24Tg001lj2=Tg002LR2j1>Tg002lR3j23Tg003Hj22Tg003cj11Tg004Hj1[Tg004fj1WTg005Ij1FTg005kj1Uj2:Tg006QR4j1CTg0071j3HTg007Oj4OTg0083j2ITg008kj27Tg009Mj30Tg009gj4NTg00:Cj29Tg00:]R5j2\Tg00;5j28Tg00;Rj1XTg00<7j2VTg00<Yj2GTg00=3j1?Tg00=Rj2;Tg00>;j3<Tg00>dj2KTg00?Pj1TTg00@0j3ETg00@Pj2DTg00@nj4STg00ALj1RTg00Ajj1QTg00BUj2@Tg00C8j1PTg00C]j45Tg00DHj2mTg00Dkj7lTg00EOj1kTg00F1j2jTg00FSj2iTg00G?j3dTg00G^j4cTg00HPj4bTg00I;j5`TP1j6JTg00I^j4aTP0j5_Tg00J:l<eTg00J_l<fTg00KDj6^Tg00Khj7]Tg00LLj7gTg00M0j8hTg00MTR0g00N2R1P0P0P4f4R4P2f3R6g00NQf2R7f1R8f0R9M<ep=ZP1P0P5P2P3g00O>f5R3P4P6P7P8P9M<fp=YP8g00O`R2g00P?R5P5g00P_R1P9E^p=BP8P2P5P5P1P9g00Q?F]p=6P7P2P5P5P1P8P9Fgp=AP6P2P5P5P1P7P8P9Ghp=L%M0g00Q_R:/491=08#>,39'2g00R=R;#1R<#1#1#1#1#1#[R=#WR>#FR?P0P>%U=R@%C8RA9H07RBCORC1I76,:=,7>90?9X5?%F0RDP0PAP7P:CNRE,70P0P>P@P9COP0%C7P6P:CN,:=,7>50?X5D1:=E,7>,9?PBP0P7PAP:1=07RB,\A18:8RE%>BRD'3PAPEP9X6018:9X60P8P81908DZPBPD190DEY%XB14:D1V:713:718:7RD=007'2147:A00D:'2'G18:6P0p-0RDg00RbRBg00SNRE#?RF#?RG#?,;0RH1;0G1;0F1;0E5<0RE5<05<0g00SmRF'KA<0HE/KF%TB5EB3E%MBP01D07P81D06CS%R0%Q0RBPBP2P5P5P11BB3P01@0;R2g00TYRF%P;,@0R;C5,6B5ABf6RE,BBP0P2PF1m0:RFC5,6B5ABFl%k5R5PBP0PFg00U@P;C5,6BP0P;g00UgR;1@0<R<C5,6B5ABP5P0P2P;P<C5,6BCLCL1jB1P9P7g00VNRBg00VnR1'91i97=0B1dAd0:8Ccb:b;b<X20X30X40X0DW1A0097,26A009:,24'G14:61367'21376[[^20^30^40^0D^1DP9143:13:3P31=0E#>P8P7P4O7b9b@b8b=CbD`EJ1I87,:=,7>90?CeP0P>P@P7Ca=H>AP0P>P@PAP7D_EJW7X>0W?o"). Qed.

Lemma Forall_upd_nat : forall (P : Z -> Prop) n v l, Forall P l -> P v -> Forall P (upd_nat n v l).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_cl ()) [] "p'0h01ni001nh12H0h22H1h31li011lh42Hlh52Hxh61eh71Hh82Hvh92H2h:2IHh;1Ph<2l0h=1vh>1xi021xh?2x0h@1zi031zp;1p;2p;3p;6g0010R0j1ATg00?Pj1;Tg00WNj28Tg009Mj31Tg00Woj6=Tg00XKj2<Tg00Xjj65Tg00YGj64Tg00Yhj37Tg00=3j1:Tg000Rj69Tg00:Cj2@Tg00Zcj6?Tg00[ER1j36Tg00@0j3>Tg00MTR2f1R3f0R436p=3f3R5f2R6?734562p=2A>234p=0p-0R7\2g00N2R8%A2R9P2f5R:/33f6R;f4R<O1f7R=P6P:P5C2[[^08X39%;2R>,3<P:P5O1P8P=P4P:P>C2P6182;f8R?,82X08P4O1n0110000020010100W8W7X0813;3P=P:O1P?P6P;P5C2[[^081056R@,3=P?P;O1P1P2f9R110=;RA9193f<RBP:f:RC10?=C2RD[P310:<RE919>10;:RF919>P9P>P0P2P7P4g00[fg00\BR7n10110100020020000000X69g00\_PAP4E=P71<D4b2W1P4O1W1f?RDP3O1f@R7/33f=R>/0B919@10<5f>R@/0>519P9P9P0P2P9P4P:P4n10110100020020103101X69PE10D@P4E5A19<@P9P2P0P2P2P4P=P3n10110100020020103101X69PF107DP3E5A12;7fA912=P4fBR=912?P2fCR7A1917R7fIR;P3O1fJRDf;R0'3fKR@fDR:P;fGR>fFRB'0RGC2]4]5[X@2A19?=P4P7P9P:PDPBO113@3fLR7fER?PDfHRH/0>RIC2]4]5X39P;P?O113D?P8P7P4PDPIC2P:P2P@P;PBP=P4E4P@g00SNP;PGC2eP2fMRGP;A74@HP5P>P4P6P:O3E4PG%:4P@10;HC2eX08P4O1n0110000020010100W4W5PCP4E9b9W2P1P4E9b2W1P4O1b2P4O1b2W1P4P6P3O3W1W4W5X<9X?2P5P6P3P4O4n200210100000020041102101000000A194FP0P<P1PAC2[X39PEO1P41@9FO1b1W8W7X08W:X39X>2P4P6E?W3X=2W0W;o"). Qed.

(* [comment removed for export] *)
Lemma cl_pw : forall w, 0 <= w <= 12 -> (bv_swrap 32 (1 ≪ (w mod 32)) mod 18446744073709551616) ≫ 1 = 2^w / 2.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_rs_cl ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh64__p1h72Hwh81Ph91wp;2p;1p;3p;4p;6p;5p;7p;8p100];p4p7210g000RR0p4p710p8g001Pj21Tg00C8j1aTg00]gj16Tg003Hj24Tg003cj10Tg004Hj1TTg00^Ej2ETg00^ej2ATg00_Lj2:Tg00_lj2;Tg00`Lj2@Tg00`ij2CTg009Mj39Tg00?Pj1ZTg0010j1XTg00aFj1WTg00ALj1VTg00Ajj1UTg00DHj2FTg00F1j2STg00:Cj2DTg00FSj2RTg00G?j3PTg00G^j4OTg002lj2>Tg00@Pj2NTg00BUj2MTg00KDj6LTg00EOj1QTg00adj5HTg00bKj4KTg00bfj3`TP0j6<Tg00cOj3JTg00d2j1_Tg00dPj2^Tg00eTj1]Tg00C]j4ITg00Khj7[Tg00LLj7\Tg00M0j8YTf0R0#0#0p=B%00#0#0#0p=G%00#0#0#0#0#0#0#0p=7g00MTR1/F0p=3P1f1R2g00UgP0CIp=?P2g00O`R3g00P?R4P4g00P_R5P0g00Q?F[p=2P1P2g00U@P0CIp=8f2R6P3P4P4P5P2P0F\p=5f3R7P3P4P4P5P6P2P0GYp==g00Q_R8/10R9g00R=R:#a#B#6R;,10R<'4R=P1P2%0:R>#GR?#TR@%6:RA/E0'A%0?#B#GRB#0#B#7#7RC#0#7#7#7#7#6RD':/;A%6>R>/@6RE/C>RF591X51P11@>2RG1A@0/:D/;A=91FX5111AGRH%6BRB,1GRGP>P8P2g00RbRI#ZRJ%XIRI%W1RK%V1RL%U1RM1F18RN%3>'?'21SM5ROP0P6g00VNRPg00VnRQ'D1R06=9PQdAP182CORQb2b3b41>8>P0b1RPp-0RRPJPI1N12RSPLPM1M1:R:,8N,2MRTPMP3P4P4P5P7ELR555M%Q4R4PTC=POPQb2b3b4X01W614921182R9[^01^6RP0116;P6P2O3b1DHP>P2P;PPPJPIPSPLPM%3;,8:,2MRP95M5P4PPC=POPQb2b3b4X01X6R142<112;[^01^6RP01186P6P2O3b1DHCK14HGP1PE1:0D/;A1@>7R7/C>RG591X51P1PE1;0A=91GX51P11@>A,CEA910GX511D1F1;EAPJPIPKPL%3ARK,8N,2MPOPQb2b3b4118AP0b19`EAE<1:EDPJPIPSPLPM18K:,2M%3B,8:,2M55MRKP4%3D,?:,2M95MTC=POPQb2b3b4X0111A0110B'4RB1>2D,49[^01P0P7P2O2R7b19JEDE<1A@EPJPIPSPLPMPKP4%_CRK#3/8:,2M%6CRC#3,?:,2M55MC=POPQb2b3b4X0111K21>2C'4\B^01P7b1,^EE<b81EA2%]2E<%6?R?,:2PJPIPSPLPMA5MTPP4%3?,?:,2M95MTC=POPQb2b3b4X011>2?,49\=^01P0P6P2O2b19J2?E<W7X91o"). Qed.

Lemma cl_srliw : forall x k, 0 <= x < 2^31 -> 0 <= k -> bv_swrap 32 (bv_wrap 32 x ≫ k) = x ≫ k.
Proof.
  intros x k Hx Hk. rewrite wrap32_small by lia. apply swrap32_small.
  assert (0 <= x ≫ k) by (apply Z.shiftr_nonneg; lia).
  assert (x ≫ k <= x) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); Z.div_mod_to_equations; nia).
  lia.
Qed.

Lemma cl_pure_err : forall ws n rank wt w, w = Znth n ws -> 0 <= n < zlen ws -> 12 < w ->
  collect_loop (skipn (Z.to_nat n) ws) rank wt = Err ZSTD_error_corruption_detected.
Proof.
  intros ws n rank wt w EW NR K. rewrite collect_step by lia. rewrite <- EW.
  replace (HUF_TABLELOG_MAX <? w) with true by (symmetry; apply Z.ltb_lt; unfold HUF_TABLELOG_MAX; lia). reflexivity.
Qed.

Lemma cl_pure_step : forall ws n rank wt w, w = Znth n ws -> 0 <= n < zlen ws -> 0 <= w <= 12 -> zlen rank = 13 ->
  0 <= Znth w rank < 2^31 -> 0 <= wt < 2^31 ->
  collect_loop (skipn (Z.to_nat n) ws) rank wt =
  collect_loop (skipn (Z.to_nat (n + 1)) ws) (upd_nat (Z.to_nat w) (Znth w rank + 1) rank) (wt + 2^w / 2).
Proof.
  intros ws n rank wt w EW NR W RL RW WT. rewrite collect_step by lia. rewrite <- EW.
  replace (HUF_TABLELOG_MAX <? w) with false by (symmetry; apply Z.ltb_ge; unfold HUF_TABLELOG_MAX; lia).
  unfold load, store, shl32, Zupd, FseNCount.Zlength.
  replace ((0 <=? w) && (w <? Z.of_nat (length rank))) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  replace ((0 <=? w) && (w <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  cbn [bind]. unfold u32.
  assert (PW : 1 <= 2^w <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 w ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  assert (PH : 0 <= 2^w / 2 <= 2048) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (Z.mod_small (Znth w rank + 1)) by lia. rewrite Z.mul_1_l, (Z.mod_small (2^w)) by lia.
  rewrite (Z.mod_small (wt + 2^w / 2)) by lia. reflexivity.
Qed.

Ltac cl_fact := first [ lia | Z.div_mod_to_equations; lia ].

Ltac cl_ck K :=
  zify_cond K; exfalso;
  repeat match type of K with context [Z.lxor ?x 18446744073709551615] => rewrite (zb_lxor_ones x) in K by lia end;
  cl_fact.

Ltac cl_chk := let K := fresh "KC" in first [ if_cases K; [ cl_ck K | ] | if_cases K; [ | cl_ck K ] ].

Section CL.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x11 x13 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word).
  Variables (m : fmem) (HW RK : Z) (ws : list Z).
  Variable POST : machine_state -> Prop.
  Hypothesis HWS : 1 <= zlen ws <= 255.
  Hypothesis HWB : Forall (fun c => 0 <= c < 256) ws.
  Hypothesis HHW : 0 < HW /\ HW + 256 <= 2^64.
  Hypothesis HRK : 0 < RK /\ RK + 52 <= 2^64.
  Hypothesis DHR : HW + 256 <= RK \/ RK + 52 <= HW.

  (* [comment removed for export] *)
  Definition cl_inv (m1 : fmem) (rank : list Z) : Prop :=
    u32arr usegs m1 RK (map (Z_to_bv 64) rank)
    /\ bytes_at usegs m1 HW (map (Z_to_bv 8) ws)
    /\ munch [(RK, RK + 52)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1.

  (* [comment removed for export] *)
  Definition cl_ok (n : Z) (rank : list Z) (wt : Z) : Prop :=
    zlen rank = 13 /\ Forall (fun v => 0 <= v <= n) rank /\ 0 <= wt <= n * 2048.

  Notation ST pc mm x5 x6 x7 x14 x17 x28 :=
    (MS (mkR ra sp gp tp x5 x6 x7 (Z_to_bv 64 RK) (Z_to_bv 64 HW) (Z_to_bv 64 (-20)) x11 (Z_to_bv 64 (Z.lxor HW 18446744073709551615)) x13 x14
             (Z_to_bv 64 1) (Z_to_bv 64 12) x17 (Z_to_bv 64 (zlen ws)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Lemma cl_loop : forall f n rank wt m1 (x7 x28 : word),
    Z.of_nat f = zlen ws - n -> 0 <= n < zlen ws ->
    cl_ok n rank wt -> cl_inv m1 rank ->
    (forall m2 rank' wt' (y5 y6 y7 y17 y28 : word),
       collect_loop (skipn (Z.to_nat n) ws) rank wt = Ok (rank', wt') -> cl_ok (zlen ws) rank' wt' -> cl_inv m2 rank' ->
       evt usegs POST (ST 0x1ef58 m2 y5 y6 y7 (Z_to_bv 64 wt') y17 y28)) ->
    (forall m2 rank' (y5 y6 y7 y14 y17 y28 : word),
       collect_loop (skipn (Z.to_nat n) ws) rank wt = Err ZSTD_error_corruption_detected -> cl_inv m2 rank' ->
       evt usegs POST (ST 0x1f124 m2 y5 y6 y7 y14 y17 y28)) ->
    evt usegs POST (ST 0x1ef08 m1 (Z_to_bv 64 (n + 1)) (Z_to_bv 64 n) x7 (Z_to_bv 64 wt) (Z_to_bv 64 30) x28).
Proof using All.
  induction f as [|f IH]; intros n rank wt m1 x7 x28 EF NR OK INV KOK KERR; [lia|].
  destruct OK as (RL & RB & WT). destruct INV as (RKA & HWA & MU & WM & MI).
  pose proof (byte_Znth ws n HWB ltac:(lia)) as WB.
  remember (Znth n ws) as w eqn:EW.
  zstep. cl_chk. zstep.
  pose proof (src_rd usegs m1 HW ws n HWA ltac:(lia)) as RD. rewrite <- EW in RD.
  zstep. cbv beta. rewrite ?(byte_lit w) by lia.
  zstep. if_cases K0; zify_cond K0.
  { eapply (KERR m1 rank); [ eapply cl_pure_err; [exact EW | lia | cl_fact] | ].
    split; [exact RKA | split; [exact HWA | split; [exact MU | split; [exact WM | exact MI]]]]. }
  assert (W12 : w <= 12) by cl_fact.
  pose proof (Forall_Znth _ rank w RB ltac:(lia)) as RW. cbv beta in RW.
  assert (PW : 1 <= 2^w <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 w ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
  assert (PH : 0 <= 2^w / 2 <= 2048) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  rewrite (cl_pure_step ws n rank wt w EW ltac:(lia) ltac:(lia) RL ltac:(lia) ltac:(lia)) in KOK, KERR.
  assert (OK' : cl_ok (n + 1) (upd_nat (Z.to_nat w) (Znth w rank + 1) rank) (wt + 2^w / 2)).
  { unfold cl_ok. split; [rewrite upd_nat_length; exact RL|]. split; [|lia].
    apply Forall_upd_nat; [|cbv beta; lia]. eapply Forall_impl; [ | exact RB ]; cbv beta; intros a Ha; lia. }
  zstep. try replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  zstep. zstep. cl_chk. zstep. cl_chk.
  pose proof (u32arr_read usegs m1 RK _ w _ _ RKA (nth_map_Znth rank w ltac:(lia)) ltac:(lia) eq_refl) as RD2.
  zstep.
  rewrite ?(sx32_small (Znth w rank)) by lia.
  zstep.
  rewrite ?(swrap32_small (Znth w rank + 1)) by lia.
  pose proof (u32arr_store_ok usegs m1 RK _ w (wa (RK + 4 * w)) RKA ltac:(rewrite length_map; lia) eq_refl) as SOK.
  zstep.
  pose proof (u32arr_write usegs m1 RK _ w (Z_to_bv 64 (Znth w rank + 1)) RKA ltac:(rewrite length_map; lia)) as S2.
  clear RKA. store_done.
  rewrite <- (map_upd_nat (Z_to_bv 64)) in S2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (INV' : cl_inv mm (upd_nat (Z.to_nat w) (Znth w rank + 1) rank))
      by (split; [exact S2 | split; [exact HWA | split; [exact MU | split; [exact WM | exact MI]]]]);
    pose proof (src_rd usegs mm HW ws n HWA ltac:(lia)) as RD3 end.
  rewrite <- EW in RD3.
  zstep. cbv beta. rewrite ?(byte_lit w) by lia.
  zstep. cl_chk.
  zstep. rewrite (sllw_pow2 w) by lia.
  zstep. try rewrite (Z.mod_small (2^w)) by lia. rewrite (cl_srliw (2^w) 1) by lia.
  replace (2^w ≫ 1) with (2^w / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  zstep. first [ rewrite (swrap32_small (2^w / 2 + wt)) by lia | rewrite (swrap32_small (wt + 2^w / 2)) by lia ].
  try replace (2^w / 2 + wt) with (wt + 2^w / 2) by lia.
  zstep. zstep. rewrite ?(Z.mod_small (n + 1)) by lia.
  zstep. rewrite ?(Z.mod_small (n + 2)) by lia.
  zstep. if_cases K1; zify_cond K1.
  all: try replace (Z_to_bv 64 (n + 2)) with (Z_to_bv 64 (n + 1 + 1)) by (f_equal; lia).
  all: first [ eapply (IH (n + 1) (upd_nat (Z.to_nat w) (Znth w rank + 1) rank) (wt + 2^w / 2));
                [cl_fact | cl_fact | exact OK' | exact INV' | exact KOK | exact KERR]
             | eapply (KOK _ (upd_nat (Z.to_nat w) (Znth w rank + 1) rank) (wt + 2^w / 2));
               [ replace (Z.to_nat (n + 1)) with (length ws) by cl_fact; apply collect_end
               | replace (zlen ws) with (n + 1) by cl_fact; exact OK'
               | exact INV' ] ].
Qed.
End CL.
