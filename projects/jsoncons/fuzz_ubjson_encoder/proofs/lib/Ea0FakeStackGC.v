(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib MemSplit As0StepLib Ea0MemIsZero Ea0RegionPoisoned
  Ea0AsanMemset Ea0AsanMemcpy Ea0StrlenIcpt Ea0TlsGetAddr.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r48448_48dd8 Ea0_code_r69818_698c8 Ea0_code_r69654_69674.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_Ea0FakeStackGC () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3powK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C56Stdlib6ZArith6BinInt1Z9mod_smallK46Stdlib9micromega7EnvRing5PExpr07C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7StepTac6u_Z2bvC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_sllC13~~~C56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_srlC13~~~C45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedI47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2or00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec6wbytesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec<wbytes_belowC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7CatExec<wbytes_aboveC13~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr0:K47Corelib4Init9Datatypes4prod01K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_addiC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4mkstC13~~~K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8step_sllC13~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5aluop03K47Corelib4Init5Logic4True01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec8step_srlC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr5instr0=C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6v_subwC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9step_subwC13~~~K4ELinuxProcessSemantics5Riscv5Instr5aluop02C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes3nat02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec3rdnC13~~~K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z=pow_le_mono_rK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z9pow_add_rC47Corelib4Init5Logic6eq_indC79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega=RingMicromega3Op201c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>Ea0FakeStackGC8gc_factsC13~~~I47Corelib4Init5Logic2ex00C47Corelib7Classes?RelationClassesBPreOrder_ReflexiveC47Corelib7Classes?RelationClasses;reflexivityC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z;le_preorderI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib9micromega7EnvRing5PExpr06C45stdpp9bitvector;definitions8bv_swrapC45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC47Corelib4Init5Logic6eq_sym".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma v_sll_lit : forall i k, (0 <= k < 64)%Z -> (0 <= i < 2 ^ 64)%Z -> v_sll (Z_to_bv 64 i) (Z_to_bv 64 k) = Z_to_bv 64 (i * 2 ^ k).
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) [] "h04__x1h14__p1h27__arithh36__sat0h46__sat1h54__ffh68__varmaph75__with81zh92Hah:2Hih;2Hkh<1ih=1kp;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j14Tg001_j1@Tg002=j20Tg002Yj23Tg0034j2>Tg003Qj1RTg003oj1KTg004Rj22Tg0058j2?Tg005bj2=Tg006Bj27Tg006bj2ATg007?j35Tg007Yj2CTg0083j2WTg008[j3VTg009?j1UTg009_j1TTg00:?j2QTg00:]j1OTg00;;j1NTg00;fj2:Tg00<Ij2JTg00<lj4;Tg00=Wj6ITg00>;j1HTg00>]j2LTg00??j2GTg00?kj3FTg00@Jj4MTg00A<j3ETP0j68Tg00Aej3PTg00BHj3DTg00Bkj3BTg00D4j2STg00E=j2[Tg00EYj7ZTg00F=j7YTg00Faj8XTg00GER0f0R1'[p=1f1R2g00GcR3g00HBR4P4g00HbR5P1g00IBFZp=<f2R6P3P4P4P5P2P1FYp=6f3R7P3P4P4P5P6P2P1GXp=9g00IbR8%11R9g00J@R:#4R;#4#4#4#4#4R<#@R=,01R>'3R?%16%@;R;/>=R@,06'3P8P7%R<R<#KRA12<7RB,?<RC/==,71,2<f4RD1>;7'A,2<RE35X88P8P61=1=,7D,2<=5AEX88P8P617D1,2<=5AEX88P81>;6,A7RF12<1=5AEX8812<FRF,CA17761W;=RE100;%1=100@[[RG%1;RHg00JeRIAV;=2UW9RJ%1@\I^9HRHp-0RIg00KARK#URL%TKRK1Q82RM%O8RN%N8ROP81:80g00Km1J8:R:C;,<ORPPOP3P4P4P5P7EIR356O%H4R4PPC91LO5R5P1P6g00LTRQg00M4RR'C1G16=5QRdAF802CMR0b5b6b7X08W1RR1392%12R9[^08^1IRQP1f5RS/0=PSPDO3b2b3b4RT9E76E81=6=PEPGPJPHPLPKPMPNPOP8P:g00MTRU1:8=C;,<ORV96OPRPP4PPC9P5P0b5b6b7X08102=,39\?^08P1PSPDO2b2b3b49P6=E812<6R=,?<PEPGPJPHPLPKPMPNPOA6O3VP4P8P:PU1:8;=D8<C;,<OR<C9P5P0b5b6b7X08X1I132>102@R>[^08^1IP1%1SPSPDO3b2b3b49B6TE8PCPEPGPJPHPRPQP1f6RQ/0@PQP7O3b2b3b4PEPGPJPHPLPKPMPNPOA6O3<P4P<C9P5P0b5b6b7X08X1I101@,32P>[^08^1IP1%1QPQP7O3b2b3b45B7E81SB==5AFeW:W;X=8W<o"). Qed.
Lemma v_srl_lit : forall i k, (0 <= k < 64)%Z -> (0 <= i < 2 ^ 64)%Z -> v_srl (Z_to_bv 64 i) (Z_to_bv 64 k) = Z_to_bv 64 (i / 2 ^ k).
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) [] "h04__x1h14__p1h27__arithh36__sat0h46__sat1h54__ffh68__varmaph75__with81zh92Hah:2Hih;2Hkh<1ih=1kp;1p;2p;3p;4p;6p;7p;8g001:j14Tg001_j1@Tg002=j20Tg002Yj23Tg0034j2>Tg003Qj1RTg003oj1KTg004Rj22Tg0058j2?Tg005bj2=Tg00N;j27Tg00N[j2ATg007?j35Tg007Yj2CTg0083j2WTg008[j3VTg009?j1UTg009_j1TTg00:?j2QTg00:]j1OTg00;;j1NTg00;fj2:Tg00<Ij2JTg00<lj4;Tg00=Wj6ITg00>;j1HTg00>]j2LTg00??j2GTg00?kj3FTg00@Jj4MTg00O8j3ETg000\j68Tg00Aej3PTg00BHj3DTg00Bkj3BTg00Oaj2STg00E=j2[Tg00EYj7ZTg00F=j7YTg00Faj8XTg00GER0f0R1'[p=1f1R2g00GcR3g00HBR4P4g00HbR5P1g00IBFZp=<f2R6P3P4P4P5P2P1FYp=6f3R7P3P4P4P5P6P2P1GXp=9g00IbR8%11R9g00J@R:#4R;#4#4#4#4#4R<#@R=,01R>'3R?%16%@;R;/>=R@,06'3P8P7%R<R<#KRA12<7RB,?<RC/==,71,2<f4RD1>;7'A,2<RE35X88P8P61=1=,7D,2<=5AEX88P8P617D1,2<=5AEX88P81>;6,A7RF12<1=5AEX8812<FRF,CA17761W;=RE100;%1=100@[[RG%1;RHg00JeRIAV;=2UW9RJ%1@\I^9HRHp-0RIg00KARK#URL%TKRK1Q82RM%O8RN%N8ROP81:80g00Km1J8:R:C;,<ORPPOP3P4P4P5P7EIR356O%H4R4PPC91LO5R5P1P6g00LTRQg00M4RR'C1G16=5QRdAF802CMR0b5b6b7X08W1RR1392%12R9[^08^1IRQP1f5RS/0=PSPDO3b2b3b4RT9E76E81=6=PEPGPJPHPLPKPMPNPOP8P:g00MTRU1:8=C;,<ORV96OPRPP4PPC9P5P0b5b6b7X08102=,39\?^08P1PSPDO2b2b3b49P6=E812<6R=,?<PEPGPJPHPLPKPMPNPOA6O3VP4P8P:PU1:8;=D8<C;,<OR<C9P5P0b5b6b7X08X1I132>102@R>[^08^1IP1%1SPSPDO3b2b3b49B6TE8PCPEPGPJPHPRPQP1f6RQ/0@PQP7O3b2b3b4PEPGPJPHPLPKPMPNPOA6O3<P4P<C9P5P0b5b6b7X08X1I101@,32P>[^08^1IP1%1QPQP7O3b2b3b45B7E81SB==5AFeW:W;X=8W<o"). Qed.

Lemma u_Z2bv8 : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) [] "h04__x1h11zh22Hzh37__arithh44__ffh58__varmaph65__witp;2p;1p;3p;4p;7p;8p;6g00E=j23Tg001:j10Tg001_j1>Tg002=j24Tg002Yj26Tg003Qj1MTg00Pjj2?Tg007?j35Tg009?j1<Tg009_j1;Tg00:?j28Tg00:]j19Tg00;;j1:Tg00;fj27Tg00<Ij2NTg00<lj41Tg00F=j7LTg00>;j1KTg00Faj8@Tg00>]j2ATg007Yj2BTg00??j2=Tg00?kj3CTg00@Jj4DTg00QPj3ETg004Rj2FTg0058j2GTg00R<j2HTg000\j6ITg00EYj7JTf1R0g00GcR1g00HBR2P2g00HbR3f0R4g00IBFJp=2g00IbR5g00GER6/34g00J@R7#0#0#0R8#0#0#0#0#0#>R9,44'6R:P5%M8R8/?0f2R;9554X15g00KAR<#<%;<1850%95%:5R<P1P2P2P3P<P1P2P2P3P51756g00Km1N57R7C1,2<P5P7g00MT1759C1,2<FLR7%K2P7G@1A<3P4P;g00LTR<g00M4R3'B1=4;=5<3dAC560CDb4b5b6X0513601409'6\:^05P4P;P0O2b39E801F80,G81H80EIW2W1o"). Qed.

Lemma wbytes_out_any_gc : forall bs m (addr x : word),
  (bv_unsigned addr + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  (bv_unsigned x < bv_unsigned addr \/ bv_unsigned addr + Z.of_nat (length bs) <= bv_unsigned x)%Z ->
  wbytes m addr bs x = m x.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) [] "h02Hxh11Hh23Hnwh34addrh42bsh51mh61xp;1p;2p;4p;3p;6p;5g001:j10Tg003Qj19Tg003oj18Tg009_j1;Tg00Rkj1ATg0058j25Tg00SMj23Tg00Smj12Tg00TMj21Tg001_j17Tg0034j2:Tg00E=j24Tg002=j26Tg00TjR0j2@Tg00UDj4?Tg007?j3>Tg00VMj6<Tg00W\j5=Tg00J@#0R1#0#0R2#9#8R3#;%02#0#0R2#9R4#8R5%A3R6[f1,54R7f3R8,33#2'1%71%72':'4f2,54R2,67f4R1,33#2,12/47'@P01548R0,62f5R7,33#2,10/42P7P1f6R2P8C?P7P8O15>6f0R61541R4,60f7R9P2P7P1P8P6E<W0P6O11332#2,14/40P9P2P7P1P6D=W0P6O1n200100000021000010000W1W2X65X35W5W4o"). Qed.

Section FPX_0. Context {fx : PropExec.FPState}.
Lemma step_sll_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SLL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_sll (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) ["FPX_0"] "h01bh12Hdh22Heh32Hfh43Hrdh52Hvh61mh73memh82pch92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1vh@1wp;1p;2p;3p;4p;5p;6p;=g009_j1LTg001:j12Tg00Xkj1DTg003Qj16Tg003oj17Tg0000j2GTg00Rkj18Tg00YPj2CTg00ZRj2=Tg007?j30Tg00[4j1@Tg00\4j2?Tg00\Tj1>Tg00]Ej4KTg001_j1JTg00^1j4ITg00^Qj3FTg00_4j3<Tg00_aj23Tg00D4j29Tg00`ij1ETg00b1j34Tg00c;j2;Tg00dEj51Tg00eMj25Tg007Yj2BTg000\j6:Tg00fUj2HTg00gQl=ATg00h]#Lg00J@#2R0#D#6R1%20R0#2R2#2#2R3#2#6#7R4'GR5%62#7#8\4R2%63#7R3%71R6%83f9R7f7R8'Cf4R9,=330g00LTR3f5R:#@g00i\R;30g00j<R<g00IbR='?R>#8f6R?#>P<P=g00jhP:P9f3R=CK%J0R0CI,=>30g00GEg00kT5F1R>9<1?=03;f<R</3?13<:'9=049g00l0R@#ERAp,2fxRBP3P5f8RC=<1>R>f=R11318131?'9RD941Cn01000000200001;<0REf;RFf:RGD1,5@f0RHPBf>RI?47?1;10R0P<PFD1,5@RJ50AX6AP3P;PBP3P5PHPI13IC13I8'994I7n0100000020000P0P<PFD1,5@=0AJX03P4P:PBA4I7HP0P<PFD1,5@=0AJX04PBA41C:PEPFPGD1,5@,BAPDPHE:P>f1E:PBP1P<PFPGD1,HIPBPIP1P<PFPGP7PCP8P?P9P=f2M=AE:W5W4W1W2W3X?4X=6X<6W9W@X;2W7X84W:W>o"). Qed.
Lemma step_srl_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op ALU_SRL rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_srl (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) ["FPX_0"] "h01bh12Hdh22Heh32Hfh43Hrdh52Hvh61mh73memh82pch92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1vh@1wp;1p;2p;3p;4p;5p;6p;=g009_j1LTg001:j12Tg00Xkj1DTg003Qj16Tg003oj17Tg0000j2GTg00Rkj18Tg00YPj2CTg00ZRj2=Tg007?j30Tg00[4j1@Tg00\4j2?Tg00\Tj1>Tg00]Ej4KTg001_j1JTg00^1j4ITg00^Qj3FTg00_4j3<Tg00_aj23Tg00Oaj29Tg00`ij1ETg00b1j34Tg00c;j2;Tg00dEj51Tg00eMj25Tg007Yj2BTg000\j6:Tg00fUj2HTg00m7l=ATg00h]#Lg00J@#2R0#D#6R1%20R0#2R2#2#2R3#2#6#7R4'GR5%62#7#8\4R2%63#7R3%71R6%83f9R7f7R8'Cf4R9,=330g00LTR3f5R:#@g00i\R;30g00j<R<g00IbR='?R>#8f6R?#>P<P=g00nCP:P9f3R=CK%J0R0CI,=>30g00GEg00kT5F1R>9<1?=03;f<R</3?13<:'9=049g00l0R@#ERAp,2fxRBP3P5f8RC=<1>R>f=R11318131?'9RD941Cn01000000200001;<0REf;RFf:RGD1,5@f0RHPBf>RI?47?1;10R0P<PFD1,5@RJ50AX6AP3P;PBP3P5PHPI13IC13I8'994I7n0100000020000P0P<PFD1,5@=0AJX03P4P:PBA4I7HP0P<PFD1,5@=0AJX04PBA41C:PEPFPGD1,5@,BAPDPHE:P>f1E:PBP1P<PFPGD1,HIPBPIP1P<PFPGP7PCP8P?P9P=f2M=AE:W5W4W1W2W3X?4X=6X<6W9W@X;2W7X84W:W>o"). Qed.
Lemma step_subw_at : forall segs regs pc mem rom w rd rs1 rs2 v,
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Op32 ALU_SUB rd rs1 rs2, 4%Z) -> bv_eqb rd 0 = false ->
  v_subw (getr regs rs1) (getr regs rs2) = v ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) ["FPX_0"] "h01bh12Hdh22Heh32Hfh43Hrdh52Hvh61mh73memh82pch92rdh:4regsh;3romh<3rs1h=3rs2h>4segsh?1vh@1wp;1p;2p;3p;4p;5p;6p;=g009_j1LTg001:j12Tg00Xkj1DTg003Qj16Tg003oj17Tg0000j2GTg00Rkj18Tg00YPj2CTg00ZRj2=Tg007?j30Tg00[4j1@Tg00\4j2?Tg00\Tj1>Tg00noj4KTg001_j1JTg00^1j4ITg00^Qj3FTg00_4j3<Tg00_aj23Tg00o[j29Tg00`ij1ETg00b1j34Tg00c;j2;Tg00dEj51Tg00eMj25Tg007Yj2BTg000\j6:Tg00fUj2HTg010el=ATg00h]#Lg00J@#2R0#D#6R1%20R0#2R2#2#2R3#2#6#7R4'GR5%62#7#8\4R2%63#7R3%71R6%83f9R7f7R8'Cf4R9,=330g00LTR3f5R:#@g00i\R;30g00j<R<g00IbR='?R>#8f6R?#>P<P=g0122P:P9f3R=CK%J0R0CI,=>30g00GEg00kT5F1R>9<1?=03;f<R</3?13<:'9=049g00l0R@#ERAp,2fxRBP3P5f8RC=<1>R>f=R11318131?'9RD941Cn01000000200001;<0REf;RFf:RGD1,5@f0RHPBf>RI?47?1;10R0P<PFD1,5@RJ50AX6AP3P;PBP3P5PHPI13IC13I8'994I7n0100000020000P0P<PFD1,5@=0AJX03P4P:PBA4I7HP0P<PFD1,5@=0AJX04PBA41C:PEPFPGD1,5@,BAPDPHE:P>f1E:PBP1P<PFPGD1,HIPBPIP1P<PFPGP7PCP8P?P9P=f2M=AE:W5W4W1W2W3X?4X=6X<6W9W@X;2W7X84W:W>o"). Qed.
End FPX_0.
(* [comment removed for export] *)
Ltac stepsv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) => eapply step_sll_at with (v := vv)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) => eapply step_srl_at with (v := vv)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) => eapply step_subw_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section FPX_1. Context {fx : PropExec.FPState}.

#[local] Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.
#[local] Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.
#[local] Ltac cond :=
  rwH; unfold at_, v_addi, v_add, c_eq, c_ltu, bv_eqb, bv_ltu; imm_norm; unorm;
  first [apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge]; lia.
#[local] Ltac wval :=
  gres; rwH; unfold at_, v_addi, v_add, v_sub, v_srli; imm_norm; unorm; rewrite ?Z.shiftr_div_pow2 by lia;
  try change (2 ^ 3)%Z with 8%Z; first [reflexivity | f_equal; lia].
#[local] Ltac maddr z := match goal with |- rdn _ _ ?ad _ = _ => replace ad with (Z_to_bv 64 z) by (symmetry; wval) end.
#[local] Ltac mldq F D z R :=
  chain_step; [reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 (Z_to_bv 64 _)); [exact F | reflexivity | exact D | maddr z; exact R | exact (bytes_le_to_Z_8 _)]
    | step_simpl; vnorm].
#[local] Ltac post := repeat split; gres; rwH; try reflexivity; try (f_equal; lia); try solve_keeps_but.
#[local] Ltac mlbq F D z R :=
  chain_step; [reflexivity
    | eapply step_lb; [exact F | reflexivity | exact D | maddr z; exact R]
    | step_simpl; vnorm].
#[local] Ltac stepsdq F D aa vv oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa) (v := vv); [exact F | reflexivity | exact D | wval | gres; rwH; first [reflexivity | f_equal; lia] | oktac]
    | step_simpl].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section INNER.
  Variable M : word -> option byte.
  Variable rom : word -> option byte.
  Variables fs c nfr nlog frsz flb sparg bot : Z.      (* [comment removed for export] *)
  Variables flag rs : Z -> Z.                          (* [comment removed for export] *)
  Hypothesis Hc : (0 <= c <= 10)%Z.
  Hypothesis Hnlog : nlog = (14 - c)%Z.
  Hypothesis Hnfr : nfr = (2 ^ nlog)%Z.
  Hypothesis Hfrsz : frsz = (2 ^ (6 + c))%Z.
  Hypothesis Hflb : flb = (fs + 4096 + 32768 - 2 * nfr)%Z.                 (* [comment removed for export] *)
  Hypothesis Hfs : (0x678000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis HL : rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)).
  Hypothesis HF : forall i, (0 <= i < nfr)%Z -> rdn ASEGS M (Z_to_bv 64 (flb + i)) 1%nat = Some [Z_to_bv 8 (flag i)] /\ (0 <= flag i < 256)%Z.
  Hypothesis HR : forall i, (0 <= i < nfr)%Z -> flag i <> 0%Z ->
    rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * frsz + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs i)))
    /\ (0 <= rs i < 2 ^ 64)%Z /\ (rs i <= bot \/ sparg <= rs i)%Z.        (* [comment removed for export] *)

  Lemma nfr_facts : (16 <= nfr <= 16384)%Z /\ (64 <= frsz <= 65536)%Z /\ (nfr * frsz = 2 ^ 20)%Z /\ (0 <= nlog <= 14)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) ["FPX_1"; "INNER"] "h04__x1h14__p1h22Hah37__arithh44__ffh56__sat0h66__sat1h76__sat2h86__sat3h96__sat4h:6__sat5h;6__sat6h<6__sat7h=8__varmaph>5__with?1ih@2HRhA2HFhB4HflbhC4HnfrhD1zhE1EhF4frszhG3nfrhH4nlogp;1p;2p;4p;3p;6p;5p;7p;9p;8g00Xkj1ATg001:j12Tg001_j15Tg012^j2CTg0034j2;Tg00E=j20Tg002Yj21Tg006bj28Tg00TMj24Tg002=j27Tg003Qj1STg003oj1hTg009_j1NTg00Rkj1dTg004Rj2?Tg013;j19Tg013Zj4FTg009?j1OTg014aj3]Tg00ZRj2MTg007?j3<Tg015Aj1\Tg015Zj2[Tg00Tjj2ZTg0083j2ETg008[j3DTg00:?j2YTg00:]j1XTg00;;j1WTg00<Ij2VTg016bj3UTg017Ej3KTg00<lj4HTg00>]j2TTg007Yj2JTg00??j2kTg00?kj3jTg00@Jj4iTg017hj1gTg00;fj2QTg00=Wj6fTg00>;j1eTg018Fj5GTg018mj4>Tg000\j6cj7Rl9`Tg019Hj5bTg019kj6aTg00EYj7LTg00F=j7_Tg00Faj8^Tg00IbR0f1R1f0R23<p=6g00GER3/02p=3f2R41112'1p=B1Q02p==P1g00GcR5g00HBR6P6g00HbR7P2g00IBR8FLp=IP4P5P6P6P7P0P1g00KmP2CHP8FLp=:P4P5P6P6P7P1P2F_p=Pf3R8P5P6P6P7P4P1P2G^p=@P0g00J@R9#AR:#A#2#5R;p,1cR<'CR=p,3nfrR>%29R?#5R@/;2RA'6%2?RB#2RC#2RD#5RE/0>%2D#2RD#2#2RF#2#2#2#2RG#2#2RH#5RI,0>'1%5DRJp,4frszRK'0%2HRH#2#5RL,0K'1RM18>K%A?R?#2RN#2#5RO,;@RP'6%31101;3B3B]CXH01;@=RQ,6>P0PQp,3flbRRp,2fs%5G'4%5H'4RH18@2'C'6%32RG1724'1%SCRC#hRS#NRT#dRUg01:GRVp,1MRW%SDRD14R1'?g01;T#9RXCFp,4flagP1O1RY,?C%OS5]S,MT3<%3Y%5F,7Y3BRF[^?01728,1GA<0Y3#\RYPVPW18<P,4HRS184K'4%2:R:#2#2#5RC'4,?D%9X#9#9#9#9#9#9RXCFp,2rsP4O1RZ,?D,[X,MTRT5<U%3Z1;@JR[,7Z'1p,3bot,0Zp,5sparg/0Z'Z'1RZ'1[R\[^?010E8108I'1188K/6P%3=R]10=;R^'1R_'17BM]@]A]BXG018@Q,CH,6R172Q,1GRRPF[^?0P\\R^?0P0%5:R:/4<R\,;@RFPVPW1848,4S/4C,?DPXCF=<UT/1Z\Y\R^?010EQRH10QIRI'1RM10J1101L'118Q1/6P/1_3B]@XF0PVPW184F,4S/4C,?DPXCF=<UT/1Z\Y\R^?0%A?#A#A#5R?,E@RR173@RY%3?1;@?RZ,73[[RT%3@RUg00JeRXAD@?1UW2R?%3Z\X^2URZ1E@ORD%3O173P[\YRCAD@O1VXX2URS%3P\X^2URW1E@JRV%3J173[[\YR`AD@J1VXX2URa%3[\X^2UR[1E@=Rb173Q\]\YRcAD@=1VXX2URd%3Q\X^2URUg00KARX#ORe%NXRX1Y01Rf%X0Rg%W0RhP0%=;Ri1V09R95U0Rj%=:Rk=K09Rl5K0g01<3%=OCH'I1Th7RmP2P4g00LTRng00M4Ro'J1k24=<nodAj031CiRob4b=b>X001C;214:2'4/6O^00P2P<O1b3b5b6b7b8b9b:b;b<14=\Rn/6OPM10JFRJ10FLRL'1RM18QFRF/6PRQ/1_R4'1PHPIP@%5BRBP=PRPTP?PZPDPCPSPWPVP`PaP[PbPcPdPUPePX%g0PgP01Q03R3g00MT%=@CH,IhPmPob4b=b>PYP2b3b5b6b7b8b9b:b;b<RYPRPTP?PZPDPCPSPWPVP`PaP[PbPcPdPUp-0RIPePXPfPgPhPhP5P6P6P7P8EfR8%5NRN#=9:h95PhR7%e6R6%=B=:hjC@PmPob4b=b>X00W1102N,11R51C;1RH,0B[^00^1IP2%3<P<p,2HcRBO3Rpb3b5b6b7b8b9b:b;b<DGP@P=P;PYPRPTP?PZPDPCPSPWPVP`PaP[PbPcPdPUPePXPfPgPhA:h39=Ph8R8P6A:hjiC@PmPob4b=b>X00X1I11G1RG10H;[^00^1IP210<NP<PBO3RBb3b5b6b7b8b9b:b;b<R<DGC>PMP4PJPLP@P:P\PYPRPTP?PZPDPCPSPWPVP`PaP[PbPcPdPUPePXPfPgPhP8P6A:hklC@PmPob4b=b>X00X1I14:1R1,0:\G^00^1IPBb3b5b6b7b8b9b:b;b<DGP@P\PEPYPRPTP?PZPDPCPSPWPVP`PaP[PbPcPdPUPePXPfPgPhP7P6%=E9:hlC@PmPob4b=b>X00X1I101E\5^00^1IPpb3b5b6b7b8b9b:b;b<DGC>PQP_P01;@n162PXD0P0PO16APXD01J0PPnP2EcPFP@P=P\PRPTP?PZPDPCPSPWPVP`PaP[PbPcPdPUPePXPfPgPhP7P6A:h3jC@PmPob4b=b>X00X1I%3H\5^00^1IPpb3b5b6b7b8b9b:b;b<RpPRPTP?PZPDPCPSPWPVP`PaP[PbPcPdPUPePXPfPgPhP8P6A:h3lC@PmPob4b=b>X00X1I%31\G^00^1IPBb3b5b6b7b8b9b:b;b<DbEaP]P^PpP<C>C>C>C>bEW@PKp,5HfrszP2FRW@WAWBP>P2p,4Hflbp,2HFp,2HRM9`WCp,4nlogp,5Hnlogp,4HnfrFRo"). Qed.

  Definition gi_inv (rg : bvmap 5 word) (i : Z) : Prop :=
    getr rg 27 = Z_to_bv 64 i /\ getr rg 24 = Z_to_bv 64 flb /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 20 = Z_to_bv 64 c
    /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096) /\ getr rg 21 = Z_to_bv 64 (6 + c) /\ getr rg 18 = Z_to_bv 64 bot
    /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 19 = Z_to_bv 64 nlog.
  (* [comment removed for export] *)
  Definition gi_keeps (regs regs' : bvmap 5 word) : Prop := forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> getr regs' r = getr regs r.

  #[local] Ltac kp := intros r N10 N11 N12 N27; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

(* [comment removed for export] *)
End INNER.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gc_facts (c nfr frsz k1 : Z) : Prop :=
  nfr = (2 ^ (14 - c))%Z /\ frsz = (2 ^ (6 + c))%Z /\ (64 * 2 ^ c = frsz)%Z /\ (32 * k1 = 32768 - 2 * nfr)%Z /\ (0 <= k1 < 1024)%Z
  /\ Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (18446744073709551615 * 2 ^ (10 - c)))) 1023) = Z_to_bv 64 k1.

Lemma gc_facts_all : forall c, (0 <= c <= 10)%Z -> exists nfr frsz k1, gc_facts c nfr frsz k1.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) ["FPX_1"] "p'0h01Hh12Hch22k1h34__x1h41ci001ch54frszh61Eh77__arithh84__ffh98__varmaph:5__with;1eh<3nfrh=1xp&0p;1p;2p;4p;7p;8p;3p;6g001:j1KTg00Xkj1:Tg001_j1;Tg009?k100Tg009_j1wTg00:?j2sTg00:]j1lTg00;;j1hTg00;fj2XTg00<Ij2dTg00<lj4OTg00F=j7{Tg00>;j1yTg00Faj8oTg00>]j2kTg007Yj2PTg00??j2iTg007?j37Tg00?kj3fTg00@Jj4eTg01<Zj4WTg01=lj2ZTg012^j24Tg003Qj1}Tg003oj1|Tg004Rj25Tg00E=R0j2QTg002Yj20Tg002=j2<Tg01>Fj3rTg01?;j4qTg000\j7_Tg019kj6nTg01?ij2mTg01@Hj4\Tg00EYj7VTg01@bj7]Tg00TjR1j2ITg0034j2YTg00TMj2xTg006bj2RTg0058j2gTg01AFj2zTg018mj4TTg00GER2f2R3'Qf1R4f0R5'Q'0p=HP4g00GcR6g00HBR7P7g00HbR8P5g00IBR9FVp=^g00IbR:/X5p=~P:P4g01<3R;P5COp=vP:P4P;1X:5COp=uP3P6P7P7P8P:P4P;P5COP9FVp=tf4R<P6P7P7P8f3R=P6P7P7P8P:P3P;1X:4COP9FVP5F]p=Nf6R;P6P7P7P8f5R>P6P7P7P8P<P9FVP=P6P7P7P8P3P6P7P7P8P4P9FVP5F]F]p=pA7:52p=[A7:45p=2A7:><A7:=3A7:45'I'Ip=LA7:<=A7:34/I5'Ip=31I45,I3p=c1445,Y3p=11x45,Y3p=6%K5#Kp=Uf7R9=7:;A7:><A7:=3A7:45'I'I'Ip=M1R45,43p=9%:5#:p=b%:5#:#:#:p=a%:5#:#:#:#:#:#:#:p=S1R=3,5<,g>/z4,5;=795p=81Q2=1<34'0/05p=G1Y;>,R9=7:<1R=3=7:4/05'0p=FA7:<=A7:34/05'0p=E1Q25p==1Y34,R==7:5p=A1R34=7:5p=>1P:5p=CP9P;P>P<P=P3CT1P45CTp=DP=P31P:4P5CTp=BP;P>P<P=P3P4P5CTCTp=?A7:><10=31P:4P5CTp=@P:P>P<P=P3P4P5F_p=JA7:=3A7:45'Ip=`1Q45,03p=jg00J@R?#KR@#:RA#K#;RB9H55RCg00KARD$00%wD1s:4%l:%h:RDP6P7P7P8PDP6P7P7P8P:1X:2R6g00KmRE1d:?RFCO,^DP:PFPE%~BRECO,^DF{%y7PDPD1vF6PDPD%;?R6,uFPDPDPF%;@R7PDPDPF%:?R?#;RGPDPDPF%K@R@#;RHPDPDPF%;ARAPDPDPF%K?#;RIPDPDPF%:?R?#;RJPDPDPF%K@RK#;RLPDPDPF%:@#;R@AtDFEDNDNDNDNDNDNDNDNFpGo1kD8P5P3g00LTRDg00M4R8'P1i53=7D8dAf:24Ceb8b9b:X3:%[41246P4P7P4PGP4PHP4PAP4PIP4PJP4PLP4P@P4PBELD3D3D33cR8\C^3:P5P3P4O2b7P8P:P>P3P4P5CWX2:,Z:X5:,Z:X<:%K?#;R8=173RDP:P<A178<P4P5CWX2:,Z:X5:A67I3REP:P=A178=RFA67I=RMP5CWX2:%UKRK#KRN#U#URO#;RPA17B3'4RQP1%[3P3P6P3P7P3PGP3PHP3PAP3PIP3PJP3PLP3P@P3PBGMD3D3D3PFPFPMPM%;NRRP7P=PM%;KRKA17B=RM,4PRS%KO#U#U#;RO?97FPSPSPP%}NRN#|RFPNPNPN%:?#b#aR?#b#a#S#S#S#S#S#S#;RTPM%;?R?15NSG8CGGFDEP5%[=P:P2A1784RSPSA67I4RMPMPRP7P4PMPKA17B4R4,4PRMA9O7SPMPMPPPFPNPNPNPTP4P?15NMG8CGGFDE^1CX4:RC1Q22%=BRM'0A1782R4P4A67I2RS/2SRUPRP7P2PSCARVA17B2R2,4PRWA9O74RX5>KRY%=WRZ1<WPR['0R\PFPNPNPNPTP2P?15NWR2G8R]'0R^'0R_'0R`P4PUP`%CSRSPVP_PSPYP^PXP\P]PZP[P:P0g01Ad9r:0PWCqg01BIRWg01BoR0'PR[PFP2GDCBF?E@W1P<P5P=F_W0P5O1P=P6P=P7P=PGP=PHP=PAP=PIP=PJP=PLP=P@P=PBGMD3D3D3P112<6P<P7P<PGP<PHP<PAP<PIP<PJP<PLP<P@P<PBELD3D3D3A178>R<P<A67I>R=P=PRP7P>P=PKA17B>R=,4PR2A9O7<P2P2PPPFPNPNPNPTP=P?15N2G8CGGFDEP512>6P6PCAH66BA1786R2P2A67I6R=/2=R<PRP7P6P=CARZA17B6R6,4PR]A9O72R\5>KRX%=]R^1<]PRY'0RSPFPNPNPNPTP6P?15N]R]G8R6'0R_'0RV'0R`P2P<P`%C=R=PZPVP=PXP_P\PSP6P^PYg01CURY97W0PWP0PWp-0P5g01D;R0g00JeP0n011000003000000X;Wg00kTPYP5EnP01m05b0W=R0P^dP[PFP]GDCBF?E@W1P;P5P>EJW0P5O1P>P7P>PGP>PHP>PAP>PIP>PJP>PLP>P@P>PBELD3D3D3P112;7P;PGP;PHP;PAP;PIP;PJP;PLP;P@P;PBGMD3D3A1789R;P;A67I9R>P>PRP7P9P>PKA17B9R>,4PR]A9O7;P]P]PPPFPNPNPNPTP>P?15N]G8CGGFDEP51297P7PCAH77BA1787R]P]A67I7R>/2>R;PRP7P7P>CAR^A17B7RY,4PRWA9O7]R65>KRS%=WR\1<WPR_'0RXPFPNPNPNPTPYP?15NWRWG8RY'0R='0RV'0RZP]P;PZ%C>R>P^PVP>PSP=P6PXPYP\P_P0P\dP[PFPWGDCBF?E@W1f8RWP5P9EJW0P5O1P9PGP9PHP9PAP9PIP9PJP9PLP9P@P9PBGMD3D3P112WGPWPHPWPAPWPIPWPJPWPLPWP@PWPBELD3D3f9RW9178R9P9A67IWR\P\PRP7PWP\PKA17BWR\,4PR_A9O79P_P_PPPFPNPNPNPTP\P?15N_G8CGGFDEP512WGPGPCAHGGBA178GR_P_A67IGR\/2\R9PRP7PGP\CARYA17BGRG,4PRXA9O7_R65>KR=%=XRS1<XPR>'0RVPFPNPNPNPTPGP?15NXRXG8RG'0R^'0RZ'0R;P_P9P;%C\R\PYPZP\P=P^P6PVPGPSP>P0PSdP[PFPXGDCBF?E@W1f:RXP5PWEJW0P5O1PWPHPWPAPWPIPWPJPWPLPWP@PWPBELD3D3P112XHPXPAPXPIPXPJPXPLPXP@PXPBGMD3f;RX9178RWPWA67IXRSPSPRP7PXPSPKA17BXRS,4PR>A9O7WP>P>PPPFPNPNPNPTPSP?15N>G8CGGFDEP512XHPHPCAHHHBA178HR>P>A67IHRS/2SRWPRP7PHPSCARGA17BHRH,4PRVA9O7>R65>KR^%=VR=1<VPR\'0RZPFPNPNPNPTPHP?15NVRVG8RH'0RY'0R;'0R9P>PWP9%CSRSPGP;PSP^PYP6PZPHP=P\P0P=dP[PFPVGDCBF?E@W1f<RVP5PXEJW0P5O1PXPAPXPIPXPJPXPLPXP@PXPBGMD3P112VAPVPIPVPJPVPLPVP@PVPBELD3f=RV9178RXPXA67IVR=P=PRP7PVP=PKA17BVR=,4PR\A9O7XP\P\PPPFPNPNPNPTP=P?15N\G8CGGFDEP512VAPAPCAHAABA178AR\P\A67IAR=/2=RXPRP7PAP=CARHA17BARA,4PRZA9O7\R65>KRY%=ZR^1<ZPRS'0R;PFPNPNPNPTPAP?15NZRZG8RA'0RG'0R9'0RWP\PXPW%C=R=PHP9P=PYPGP6P;PAP^PSP0P^dP[PFPZGDCBF?E@W1f>RZP5PVEJW0P5O1PVPIPVPJPVPLPVP@PVPBELD3P112ZIPZPJPZPLPZP@PZPBGMf?RZ9178RVPVA67IZR^P^PRP7PZP^PKA17BZR^,4PRSA9O7VPSPSPPPFPNPNPNPTP^P?15NSG8CGGFDEP512ZIPIPCAHIIBA178IRSPSA67IIR^/2^RVPRP7PIP^CARAA17BIR;,4PR6A9O7SRG5>KRY%=6R=1<6PR9'0RHPFPNPNPNPTP;P?15N6R6G8R;'0RW'0RX'0R\PSPVP\%C^R^PAPXP^PYPWPGPHP;P=P9P0P=dP[PFP6GDCBF?E@W1f@R6P5PZEJW0P5O1PZPJPZPLPZP@PZPBGMP1126JP6PLP6P@P6PBELfAR69178RZPZA67I6R=P=PRP7P6P=PKA17B6R=,4PR9A9O7ZP9P9PPPFPNPNPNPTP=P?15N9G8CGGFDEP5126JPJPCAHJJBA178JR9P9A67IJR=/2=RZPRP7PJP=CAR;A17BJRJ,4PRHA9O79RG5>KRW%=HRY1<HPR^'0RXPFPNPNPNPTPJP?15NHRHG8RJ'0RA'0R\'0RVP9PZPV%C=R=P;P\P=PWPAPGPXPJPYP^P0PYdP[PFPHGDCBF?E@W1fBRHP5P6EJW0P5O1P6PLP6P@P6PBELP112HLPHP@PHPBC`fCRH9178R6P6A67IHRYPYPRP7PHPYPKA17BHRY,4PR^A9O76P^P^PPPFPNPNPNPTPYP?15N^G8CGGFDEP512HLPLPCAHLLBA178LR^P^A67ILRY/2YR6PRP7PLPYCARJA17BLRL,4PRXA9O7^RG5>KRA%=XRW1<XPR='0R\PFPNPNPNPTPLP?15NXRXG8RL'0R;'0RV'0RZP^P6PZ%CYRYPJPVPYPAP;PGP\PLPWP=P0PWdP[PFPXGDCBF?E@W1fDRXP5PHEJW0P5O1PHP@PHPBC`P112X@12XBfERX9178R1P1A67IXRHPHPRP7PXPHPKA17BXRH,4PRWA9O71PWPWPPPFPNPNPNPTPHP?15NWG8CGGFDEP512X@P@PCAH@@BA178@RWPWA67I@RH/2HR1PRP7P@PHCAR=A17B@R@,4PRLA9O7WR\5>KRG%=LR;1<LPRA'0RYPFPNPNPNPTP@P?15NLRLG8R@'0RV'0RJ'0RZPWP1PZ%CHRHP=PJPHPGPVP\PYP@P;PAP0P;dP[PFPLGDCBF?E@W1fFRLP5PXEJW0P5O112XBPBPCAjMBBA178BR8P8A67IBRI/2IRMPRP7PBPICARRA17BBRB,4PRCA9O78RO5>KRK%=CR71<CPRP'0R;PFPNPNPNPTPBP?15NCRCG8RN'0R?'0RB'0RTP8PMPT%CIRIPRPBPIPKP?POP;PNP7PPP0P7dP[PFPCGDCBF?E@W1PLP5PXEJW0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000W0P5O1n200100001021100011000P3PDPEPQCWeC\C\C\b6W1X4:o"). Qed.

Lemma swrap32_small : forall z, (- 2 ^ 31 <= z < 2 ^ 31)%Z -> bv_swrap 32 z = z.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) ["FPX_1"] "h02Hah14__x1h27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__with81zh92Hzh:6__sat2h;6__sat3p;1p;2p;3p;4p;8p;6p;7g001:j14Tg001_j17Tg00Xkj16Tg0034j2?Tg01DXj1YTg00E=j2@Tg002=j22Tg002Yj28Tg00TMj2:Tg012^j2ATg007?j35Tg0083j2=Tg008[j3BTg009?j1VTg009_j1UTg00:?j2RTg00:]j1QTg00;;j1OTg00<Ij2MTg00;fj2<Tg003Qj19Tg00BHj3;Tg017Ej3JTg016bj3ITg00<lj43Tg00>]j2HTg007Yj2GTg00??j2KTg00?kj3LTg00@Jj4FTg005bj2ETg01E5j2NTg00>;j1DTg00Faj8PTg00Aej3CTg000\j6STg01EXj2TTg00EYj7XTg00F=j7WTg00GER0f0R1'@p=0f1R2g00GcR3g00HBR4P4g00HbR5P1g00IBFXp=1f2R6P3P4P4P5P2P1FWp=>g00IbR7g00J@R8#4R9#7R:%68#6#6#6R;#7R<'?R=#Y/@1121='8R>P71:2=R?1A1==576X871=:<R@120:RA%0<120=[[RB%0:RCg00JeRDAB:<2UW0R<%0=\D^0CREg00KARF#VRG%UFRF1R72RH%Q7RI%O7RJP71M78R81<7:RK%9;5;7R;5J7RL=I7;g01<3P8C3'11HJ5RMP1P6g00LTRNg00M4RO'G1K16=5NOdAL702CFROb3b6b7X171:1=/A==571^17P1f4O1b2b4b5%49#4#4#4R9#7R=,?:RN,E?1=:=%0=120N[\AAB:=2VDX0C%0N\D^0CP@PBP<PEPGPFPHPIPJP3P4P4P5P71N7;g00KmR5P8C3,1JP7P8g00MTR8P;C3,1J5>J%D4P71<70P5PLC3,1JP7PLP8%99R99;7KC3,1J5>JGPPMPOb3b6b7X17%0?12?N'8\>^17P1f6f5O2b2b4b5b:b;9C?NES1T92=572eW9W8o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CLASS.
  Variable mem0 : word -> option byte.       (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables t fs sparg bot : Z.              (* [comment removed for export] *)
  Variables flag rs : Z -> Z -> Z.           (* [comment removed for export] *)
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hfs : (0x678000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Hsp : (0 <= sparg < 2 ^ 64)%Z /\ (0 <= bot < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  (* [comment removed for export] *)
  Hypothesis HCF : forall M, (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x) ->
    rdn ASEGS M (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20))
    /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
          rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z)
    /\ (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
          rdn ASEGS M (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
          /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= bot \/ sparg <= rs c i)%Z).

  Definition gcl_inv (rg : bvmap 5 word) (c : Z) : Prop :=
    getr rg 20 = Z_to_bv 64 c /\ getr rg 25 = Z_to_bv 64 fs /\ getr rg 7 = Z_to_bv 64 1 /\ getr rg 8 = Z_to_bv 64 (fs + 4096)
    /\ getr rg 18 = Z_to_bv 64 bot /\ getr rg 9 = Z_to_bv 64 sparg /\ getr rg 2 = Z_to_bv 64 (t - 144).
  Definition gcl_keeps (regs regs' : bvmap 5 word) : Prop :=
    forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 27%bv -> r <> 21%bv -> r <> 24%bv -> r <> 19%bv -> r <> 20%bv -> getr regs' r = getr regs r.
  Definition out_gc (M : word -> option byte) : Prop := forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M x = mem0 x.
  (* [comment removed for export] *)
  Definition slot32 (M M' : word -> option byte) : Prop := forall x : word, ~ (t - 112 <= bv_unsigned x < t - 104)%Z -> M' x = M x.

  #[local] Ltac hide_dj := try hide Hfs.
  #[local] Ltac kp8 := intros r; intros; repeat (rewrite getr_other; [| intros ->; match goal with Hn : ?a <> ?a |- _ => exact (Hn eq_refl) end]); reflexivity.

(* [comment removed for export] *)

  (* [comment removed for export] *)
(* [comment removed for export] *)
End CLASS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WHOLE.
  Variable mem0 : word -> option byte.
  Variable rom : word -> option byte.
  Variables sp ra : word.
  Variables t fs sparg tpv key tsd ctx th top botth g48 g50 g58 g60 g40 g35 : Z.
  Variables flag rs : Z -> Z -> Z.           (* [comment removed for export] *)
  Hypothesis Hs_def : bv_unsigned sp = t.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Ht : (0x1000000 <= t - 160)%Z /\ (t < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok ASEGS mem0 (Z_to_bv 64 (t - 160)) 160%nat = true.
  Hypothesis Htp : (96 <= tpv < 2 ^ 64)%Z.
  Hypothesis Hkey : (0 <= key < 2 ^ 28)%Z.
  Hypothesis Htsd : (0 <= tsd /\ tsd + 8 * key + 8 <= 2 ^ 64)%Z.
  Hypothesis Hctx : (0 < ctx /\ ctx + 160 <= 2 ^ 64)%Z.
  Hypothesis Hth : (0 < th /\ th + 80 <= 2 ^ 64)%Z.
  Hypothesis Htop : (botth < top)%Z /\ (0 <= botth)%Z /\ (top < 2 ^ 64)%Z /\ (botth <= sparg <= top)%Z.   (* [comment removed for export] *)
  Hypothesis Hfs : (0x678000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 <= t - 160 \/ t <= fs)%Z.
  Hypothesis Hwfs : store_ok ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = true.
  Hypothesis Hg : (0 <= g48 < 2 ^ 64)%Z /\ (0 <= g50 < 2 ^ 64)%Z /\ (0 <= g58 < 2 ^ 64)%Z /\ (0 <= g60 < 2 ^ 64)%Z /\ (0 <= g40 < 2 ^ 64)%Z /\ (0 <= g35 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis HC : forall M', (forall x : word, (bv_unsigned x < t - 160 \/ t <= bv_unsigned x)%Z -> M' x = mem0 x) ->
     rdn ASEGS M' (0x141220 : word) 1%nat = Some [Z_to_bv 8 1] /\                                       (* [comment removed for export] *)
     rdn ASEGS M' (0x141224 : word) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 key)) /\
     rdn ASEGS M' (Z_to_bv 64 (tpv - 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 tsd)) /\
     rdn ASEGS M' (Z_to_bv 64 (tsd + 8 * key)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 ctx)) /\
     rdn ASEGS M' (Z_to_bv 64 (ctx + 152)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 th)) /\
     rdn ASEGS M' (Z_to_bv 64 (th + 40)) 1%nat = Some [Z_to_bv 8 0] /\                                  (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 8)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 top)) /\        (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (th + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 botth)) /\     (* [comment removed for export] *)
     rdn ASEGS M' (0x139158 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g48)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (0x139160 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g50)) /\
     rdn ASEGS M' (0x139168 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g58)) /\
     rdn ASEGS M' (0x139170 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g60)) /\
     rdn ASEGS M' (0x139150 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g40)) /\
     rdn ASEGS M' (0x10390 : word) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g35)) /\              (* [comment removed for export] *)
     rdn ASEGS M' (Z_to_bv 64 (fs + 88)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 20)) /\       (* [comment removed for export] *)
     (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z ->
          rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 - 2 * 2 ^ (14 - c) + i)) 1%nat = Some [Z_to_bv 8 (flag c i)] /\ (0 <= flag c i < 256)%Z) /\
     (forall c i, (0 <= c <= 10)%Z -> (0 <= i < 2 ^ (14 - c))%Z -> flag c i <> 0%Z ->
          rdn ASEGS M' (Z_to_bv 64 (fs + 4096 + 32768 + c * 2 ^ 20 + i * 2 ^ (6 + c) + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (rs c i)))
          /\ (0 <= rs c i < 2 ^ 64)%Z /\ (rs c i <= botth \/ sparg <= rs c i)%Z).                    (* [comment removed for export] *)

  #[local] Ltac hide_dj := try hide Hfs.
  Lemma sp_sg : sp = Z_to_bv 64 t.
Proof.
ltac2:(KReplay.run1 (kr_t_Ea0FakeStackGC ()) ["FPX_1"; "WHOLE"] "h01tp;1p;2p;3p;4p;6g001:j10Tg003Qj18Tg0058j23Tg003oj12Tg004Rj21Tg007?j37Tg01F?j26Tg01G1j44Tg019kj65Tg00IbR0g00J@#0#0#0#0#0#0#8R1p,2spR2'3R3%21R4f0,11772X00P41113P21612C4p,1tp,6Hs_defE5o"). Qed.

  (* [comment removed for export] *)
  Definition F13 (rg : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem0
      (Z_to_bv 64 (t - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (t - 16)) (word_to_le_bytes 8 (getr rg 8)))
      (Z_to_bv 64 (t - 24)) (word_to_le_bytes 8 (getr rg 9)))
      (Z_to_bv 64 (t - 32)) (word_to_le_bytes 8 (getr rg 18)))
      (Z_to_bv 64 (t - 40)) (word_to_le_bytes 8 (getr rg 19)))
      (Z_to_bv 64 (t - 48)) (word_to_le_bytes 8 (getr rg 20)))
      (Z_to_bv 64 (t - 56)) (word_to_le_bytes 8 (getr rg 21)))
      (Z_to_bv 64 (t - 64)) (word_to_le_bytes 8 (getr rg 22)))
      (Z_to_bv 64 (t - 72)) (word_to_le_bytes 8 (getr rg 23)))
      (Z_to_bv 64 (t - 80)) (word_to_le_bytes 8 (getr rg 24)))
      (Z_to_bv 64 (t - 88)) (word_to_le_bytes 8 (getr rg 25)))
      (Z_to_bv 64 (t - 96)) (word_to_le_bytes 8 (getr rg 26)))
      (Z_to_bv 64 (t - 104)) (word_to_le_bytes 8 (getr rg 27)).

(* [comment removed for export] *)
End WHOLE.
End FPX_1.
