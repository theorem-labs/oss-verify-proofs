(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_fa_iface RF_huf_y4s RF_huf_y4s_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Startup_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s0 () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit=lor_shift_addK46Stdlib9micromega=RingMicromega5Psatz07K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission6Common8FseRdKit8byte_litK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_y4s_iface3Y4SC47Corelib5Lists7ListDef3mapC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2ex00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z03I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2;x2_table_okC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7ZlengthC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef3nthC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_cell_okC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K47Corelib4Init9Datatypes6option01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC47Corelib4Init9Datatypes6lengthC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC56Stdlib6ZArith6BinInt1Z6ltb_ltC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s8y4s_epi0C56Stdlib6ZArith6BinInt1Z6ltb_geC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit6src_rdC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rK4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec4v_orC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6alu_orC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z6shiftrC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z;div_str_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=bytes_at_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le2C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit=le2_two_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4zx16K4ELinuxProcessSemantics5Riscv5Instr5instr06C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@zext_extract_le2C5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_carveC5ARocqVerifyHarness?AgentSubmission3Lib3TacArw_cells_split_CBC5ARocqVerifyHarness?AgentSubmission3Lib3Tac;mk_CB_cellsC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneK46Stdlib9micromega5Tauto8GFormula07C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem:zx16_shortC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s0;y4_le16_lorC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC56Stdlib6NArith6BinNat1N2leC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge5zr_bvC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepK45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC45stdpp9bitvector;definitions:bv_extractK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepK46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01I4ELinuxProcessSemantics5Riscv3Sem4core00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX1@HUF_TABLELOG_MAXI5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX26deltX200C5ARocqVerifyHarness?AgentSubmission4Spec=HufPure_HufX2:x2_defaultK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop03K4ELinuxProcessSemantics5Riscv5Instr5aluop09K4ELinuxProcessSemantics5Riscv5Instr5aluop07K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5msize02K47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma y4_le16_lor : forall b0 b1, 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  Z.lor (bv_unsigned (Z_to_bv 8 b1) ≪ 8 mod 18446744073709551616) (bv_unsigned (Z_to_bv 8 b0)) = b0 + 256 * b1.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s0 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh64__p1h74__x2h82H0h92H1h:2b0h;2b1p;2p;1p;4p;3p;6p;7p;8p10000p4p7210g000\R0p4p710p8g001:j2=Tg001Vj10Tg002;j1?Tg002Yj28Tg0035j26Tg003Pj2DTg0040j2>Tg004Pj1VTg004nj2ATg005Tj2@Tg006>j27Tg006[j2:Tg0078j2<Tg007Uj2dTg0082j1`Tg008Rj1_Tg0092j2LTg009Pj1]Tg009nj4[Tg00:Lj1ZTg00:jj1YTg00;Uj2KTg00<8j24Tg00<[j3XTg00=>j3CTg00=aj3JTg00>Dj4ETg00>oj2UTg00?Qj2TTg00?kj2STg00@Wj3ITg00A1j3RTg00APj4QTg00BBj1kTg00Bdj6jTg00CHj6iTP0j65Tg00DLj2hTg00E5j1HTg00ETj2FTg00F=j3eTg00Ffj3OTg00GOj2MTg00H;j2cTg00Hgj3NTg00IGj3aTg00Ijj3bTg00JSj2PTg00KPj7fTg00L4j7^Tg00LXj8gTf0R0#0#0p=\%00#0#0#0p=W%00#0#0#0#0#0#0#0p=1g00M<R1f1R2;I0p=3P2g00MZR3g00N9R4P4g00NYR5P0g00O9Ffp=2P1P2g00OYP0CEp=GP1P2g00P@P0CEp=Bf2R6P3P4P4P5P2P0F^p=;f3R7P3P4P4P5P6P2P0Ggp=9g00PgR8/=2R9g00QER:#0R;#\R<#0#WR=#?R>,82'6R?P1P6%?<R@,D0%1=#1#1#1#1#1#1#?R='>%V<R<f4RA,A<'@'71:>7,<ARB'3X51P1P71D7@/>=/70/3BX51P1%?;RC/d@RD,:6RE1>0=/7A/3BX51P1PE170A/3BX51P11<7E130BX51g00QjRB#`RF%_BRGP11L16P2%]1RHC[%Z1RI%Y1RJP11K1:R:1K1;R;141C=X1<RC5C15J1g00RV141>RK=C1;9J1:CE'21UJ5R;P0P6g00S=RLg00S]RM'T1S06=ILMdAR182CQRMb2b3b4X01X711:2DRL,<01:>2,<0'3^01^71P0P7PAO2b117E7P6P@P7PFPGPHPI1418RH141@'G,2JP;PMb2b3b41=8@P0b1RNPFPG1L12ROPIPJ1GH:,2JRP1B:K,2J5;JRK%k4RQ1B:C,2J9;JPC9P;PMb2b3b4X011=80RR180>'6RS182D,69[^01P0PAP6O2RAb1p-0RDPFPGPOPIPJPJP3P4P4P5P7Ej9;JPPQPPC9P;PMb2b3b4X01W616R2P9[^01^6DP0187>P7P2O3b1EiE51>E=1h1>g00T=R>#HRD,F15e11F1>R>5O1g00T\R9'M%HD#H,F19O1>/M9,c>=NBF5NBPGPOPIPJPKPQAC1:CRC,GH,2J141=,BC,2J5;JC9P;PMb2b3b4X011=8L18L='6\S^01P0P7P2O2R2b19aE=E51D6@Ab6@NE51A<7,@<PFPGPOPIPJPKPQPKC9P;PMb2b3b4X01RMP?\S^01RSPAb1,P7E51A<6,@<PMPSP2b1,P6E5X9?W8X;1X:1o"). Qed.


Lemma y4z_cons : forall segs m A c rest,
  rw_cells segs m A (c :: rest) ->
  rw_cells segs m A [c] /\ rw_cells segs m (A + Z.of_nat (csize c)) rest.
Proof.
  intros segs m A c rest H.
  unfold rw_cells, cells_at, wr_at in *.
  destruct H as [[[WFc WFr] BA] (W0 & W1 & W2)].
  cbn [cells_bytes cells_size cells_wf] in *.
  apply bytes_at_app in BA. destruct BA as [B1 B2].
  rewrite (cbytes_length c WFc) in B2.
  split.
  - split.
    + split; [split; [exact WFc | exact I] | rewrite app_nil_r; exact B1].
    + split; [lia | split; [lia | intros i Hi; apply W2; lia]].
  - split.
    + split; [exact WFr | exact B2].
    + split; [lia | split; [lia | ]].
      intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia.
      apply W2; lia.
Qed.

Lemma y4z_zx16 : forall c, 0 <= c < 2^16 -> zx16 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof. intros c Hc. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Definition Y4Z_CHKS : list Z := [108696; 108708; 108716; 108728; 108744; 108752; 108764; 108780; 108792; 108824; 108856;
  108888; 108908; 108928; 108952; 108964].
Lemma y4z_lxor_m1 : forall x, 0 <= x < 18446744073709551616 ->
  Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64).
  assert (E : Z.lxor x (Z.ones 64) = Z.land (Z.lnot x) (Z.ones 64)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
    destruct (Z.lt_ge_cases n 64) as [L|L].
    - rewrite Z.ones_spec_low by lia. destruct (Z.testbit x n); reflexivity.
    - rewrite Z.ones_spec_high by lia.
      destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
      assert (Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia).
      rewrite (Z.bits_above_log2 x n) by lia. reflexivity. }
  rewrite E, Z.land_ones by lia. unfold Z.lnot. rewrite Z.ones_equiv.
  symmetry. apply Z.mod_unique with (q := -1); lia.
Qed.
Ltac y4z_land := repeat match goal with H : context [Z.land ?a ?b] |- _ =>
  lazymatch goal with _ : 0 <= Z.land a b < 2^47 |- _ => fail | _ => pose proof (land_lt_pow2 a b 47 ltac:(lia) ltac:(lia)) end end.
Ltac y4z_fix H :=
  repeat match type of H with context [bv_unsigned (Z_to_bv 8 (Znth ?k ?l))] =>
    let B := fresh "BB" in pose proof (byte_Znth l k ltac:(assumption) ltac:(lia)) as B;
    rewrite (byte_lit (Znth k l) B) in H end;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 in H by lia;
  repeat match type of H with context [(?x * 2^?k) mod ?M] => rewrite (Z.mod_small (x * 2^k) M) in H by lia end;
  repeat match type of H with context [Z.lor (?x * 2^?k) ?a] => rewrite (lor_shift_add x k a) in H by lia end;
  repeat match type of H with context [Z.land ?x 3] =>
    replace (Z.land x 3) with (x mod 4) in H by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity) end;
  repeat match type of H with context [Z.land ?x 7] =>
    replace (Z.land x 7) with (x mod 8) in H by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity) end;
  repeat match type of H with context [Z.lxor ?x 18446744073709551615] =>
    rewrite (y4z_lxor_m1 x) in H by (first [apply Z.mod_pos_bound; lia | lia]) end.
Ltac y4z_cut := exfalso; lazymatch goal with HC : _ |- _ =>
  y4z_land; first [ lia | apply HC; lia | y4z_fix HC; first [ lia | Z.div_mod_to_equations; lia ] ] end.
Ltac y4z_srcrd S bs SRC := let t k := first [
    lazymatch goal with _ : ov_read_bytes _ _ (Z_to_bv 64 (S + k)) 1 = _ |- _ => idtac
                      | _ : ov_read_bytes _ _ (Z_to_bv 64 S) 1 = _ |- _ => lazymatch k with 0 => idtac end end
  | let R := fresh "RD" in pose proof (src_rd usegs _ S bs k SRC ltac:(lia)) as R;
    first [ replace (S + 0) with S in R by lia | idtac ] | idtac ] in
  t 0; t 1; t 2; t 3; t 4; t 5.
Ltac y4z_walk target target2 SRCV SRCL SRCH :=
  repeat (lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 target) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 target2) _ _ _ _) => fail
    | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
        let b := eval vm_compute in (existsb (Z.eqb pc) Y4Z_CHKS) in
        lazymatch b with
        | true => solve [y4z_cut]
        | false => first [ zstep | y4z_srcrd SRCV SRCL SRCH; zstep ]
        end
    | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
        let H := fresh "B" in if_cases H; zify_cond H
    end).

Ltac y4z_norm :=
  repeat match goal with H : rw_cells _ _ ?A _ |- _ => match A with context [Z.of_nat ?k] =>
    let v := eval vm_compute in (Z.of_nat k) in is_Zlit v; change (Z.of_nat k) with v in H end end;
  repeat match goal with H : rw_cells _ _ (Z.add (Z.add ?b ?c) ?d) _ |- _ =>
    is_Zlit c; is_Zlit d; let v := eval vm_compute in (c + d) in replace (Z.add (Z.add b c) d) with (Z.add b v) in H by lia end.
Ltac y4z_app H k :=
  lazymatch type of H with rw_cells ?sg ?m ?A ?cs =>
    destruct (proj1 (Startup_kit.rw_cells_app sg m A (firstn k cs) (skipn k cs)) ltac:(rewrite firstn_skipn; exact H)) as [? ?];
    clear H end;
  repeat match goal with H : rw_cells _ _ _ (firstn _ _) |- _ => cbn [firstn] in H end;
  repeat match goal with H : rw_cells _ _ (Z.add _ (Z.of_nat (cells_size (firstn _ _)))) _ |- _ =>
    cbn [firstn cells_size csize Nat.add] in H end;
  repeat match goal with H : rw_cells _ _ _ (skipn _ _) |- _ => cbn [skipn] in H end;
  y4z_norm.
Ltac y4z_peel_cb :=
  repeat match goal with H : rw_cells _ _ _ (CB ?k _ :: _ :: _) |- _ =>
    lazymatch k with 40%nat => idtac | 136%nat => idtac | 160%nat => idtac end;
    destruct (y4z_cons _ _ _ _ _ H) as [? ?]; clear H end;
  repeat match goal with H : rw_cells _ _ (Z.add _ (Z.of_nat (csize _))) _ |- _ => cbn [csize] in H end;
  y4z_norm.
Ltac y4z_split4 :=
  lazymatch goal with H : rw_cells ?sg ?m ?A [CB 160 ?j] |- _ =>
    pose proof (rw_cells_split_CB sg m A [] 160 j [] [40; 40; 40; 40]%nat H eq_refl); clear H end;
  repeat match goal with H : rw_cells _ _ _ ([] ++ _) |- _ => cbn [app mk_CB_cells] in H end;
  y4z_peel_cb.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S0.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DT4 : DT mod 4 = 0.

  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation YB l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cells cbs
                      TOK ECB LCB MTL TLM D0 DP DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).
  Notation Y4F' mm spl b4 b3 b2 b1 :=
    (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).
  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation Y4S' mm := (Y4S ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT mtl tl lo src cbs mm).
  Notation L1 := (jt_len src 0). Notation L2 := (jt_len src 2). Notation L3 := (jt_len src 4).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Notation SEG := ((dcap + 3) / 4).
  Notation desc := (tl + 256 * mtl).
  (* [comment removed for export] *)
  Notation SPL436 j0 j112 :=
    [CB 96 j0; C8 (Z_to_bv 64 (DST + SEG)); C8 (Z_to_bv 64 (DST + 2 * SEG)); CB 8 j112;
     C8 (Z_to_bv 64 (DST + dcap)); C8 (Z_to_bv 64 (DT + 4))].

  (* [comment removed for export] *)
  Hypothesis HC436 : forall mm j0 j112 jb4 jb3 jb2 jb1
      (xra t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    Y4F' mm (SPL436 j0 j112) [CB 40 jb4] [CB 40 jb3] [CB 40 jb2] [CB 40 jb1] ->
    6 <= dcap -> 10 <= n -> O4 <= n ->
    t0 = Z_to_bv 64 (DT + 4) -> t1 = Z_to_bv 64 (DST + dcap) -> x8 = Z_to_bv 64 DST -> x9 = Z_to_bv 64 (SS + O3) ->
    a0 = Z_to_bv 64 (SP + -656) -> a1 = Z_to_bv 64 (SS + 6) -> a2 = Z_to_bv 64 L1 -> a3 = Z_to_bv 64 n ->
    a4 = Z_to_bv 64 DT -> a5 = Z_to_bv 64 DST -> a6 = Z_to_bv 64 L1 -> x18 = Z_to_bv 64 L3 ->
    x19 = Z_to_bv 64 (SS + O2) -> x20 = Z_to_bv 64 L2 -> x21 = Z_to_bv 64 O4 -> x22 = Z_to_bv 64 n ->
    x24 = Z_to_bv 64 desc -> x25 = Z_to_bv 64 (DST + 2 * SEG) -> x26 = Z_to_bv 64 dcap -> x27 = Z_to_bv 64 (DST + 3 * SEG) ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7
                           x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 109036) fc None mm (seg_rom usegs)).

  Ltac y4z_y4f :=
    unfold Y4F; repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | reflexivity | (eexists; split; eassumption) | (eexists; eassumption)
          | (do 12 eexists; unfold PY4_RET; eassumption) ].
  Ltac y4z_epi :=
    lazymatch goal with H : rw_cells usegs _ (SP + -912) ?cs |- evt _ _ (MS _ _ (Z_to_bv 64 121940) _ _ _ _) =>
      let k := eval compute in (length cs - 13)%nat in
      y4z_app H k;
      lazymatch goal with FA : rw_cells usegs _ (SP + -912) _ |- _ =>
        destruct (rw_cells_forget usegs _ _ _ FA) as (? & ?); clear FA end;
      lazymatch goal with FK : rw_cells usegs _ (SP + -912) [CB _ ?jk] |- _ =>
        cbn [cells_size csize Nat.add] in FK;
        pose proof (rw_cells_split_CB usegs _ _ [] 296 jk [] [136; 40; 40; 40; 40]%nat FK eq_refl); clear FK end;
      repeat match goal with H : rw_cells _ _ _ ([] ++ _) |- _ => cbn [app mk_CB_cells] in H end;
      y4z_peel_cb;
      eapply (YB y4s_epi); y4z_y4f
    end.

  (* [comment removed for export] *)
  Lemma y4s0_entry : y4_slow_goal ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT mtl tl lo src cbs.
  Proof using All.
    unfold y4_slow_goal.
    intros mm t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6
      (OUTX & SRC & TB & DTH & ST & FRS0 & MI & MU & WM).
    destruct OUTX as (buf & OUT & LB).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TOK as (TL1 & _). unfold HUF_TABLELOG_MAX in TL1.
    assert (N0 : 0 <= n) by lia.
    carve_frame 408%nat ST. rename FR into F408.
    carve_frame 400%nat ST.
    unfold PY4_BODY, PY4_RET.
    y4z_walk 109024 121940 SS src SRC.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 121940) _ _ _ _) => y4z_epi | _ => idtac end.
    lazymatch goal with H : bytes_at usegs ?m DT ?bs |- _ =>
      pose proof (bytes_at_read usegs m DT bs 2 2 H ltac:(lia) ltac:(cbn [length]; lia)) as RDT;
      change (Z.to_nat 2) with 2%nat in RDT; cbn [firstn skipn] in RDT;
      change (wa (DT + 2)) with (Z_to_bv 64 (DT + 2)) in RDT;
      rewrite <- (le2_two_bytes tl mtl ltac:(lia) ltac:(lia)) in RDT end.
    zstep.
    y4z_walk 109036 121940 SS src SRC.
    all: lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 121940) _ _ _ _) => y4z_epi | _ => idtac end.
    assert (Y0 : 0 <= Znth 0 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y1 : 0 <= Znth 1 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y2 : 0 <= Znth 2 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y3 : 0 <= Znth 3 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y4 : 0 <= Znth 4 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    assert (Y5 : 0 <= Znth 5 src < 256) by (apply byte_Znth; [exact BYS | lia]).
    repeat match goal with H : context [Z.lor (bv_unsigned (Z_to_bv 8 _) ≪ 8 mod _) _] |- _ =>
      rewrite !y4_le16_lor in H by lia end.
    rewrite !y4_le16_lor by lia.
    lazymatch goal with H : rw_cells usegs _ (SP + -912) _ |- _ => y4z_app H 6%nat end.
    y4z_peel_cb. y4z_split4.
    lazymatch goal with H : rw_cells usegs _ (SP + -912) _ |- _ =>
      rewrite Z.shiftr_div_pow2 in H by lia; change (2 ^ 2) with 4 in H;
      replace (DST + (dcap + 3) / 4 + (dcap + 3) / 4) with (DST + 2 * SEG) in H by lia end.
    eapply HC436.
    all: try unfold jt_len; try change (0 + 1) with 1; try change (2 + 1) with 3; try change (4 + 1) with 5.
    all: first [ y4z_y4f
               | lia
               | reflexivity
               | (rewrite ?Z.shiftr_div_pow2 by lia; try change (2 ^ 2) with 4; rewrite ?y4z_zx16 by lia; f_equal; first [lia | Z.div_mod_to_equations; lia])
               | (Z.div_mod_to_equations; lia) ].
  Qed.
End Y4S0.
End CANSEC1.
