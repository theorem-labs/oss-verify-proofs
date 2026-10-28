(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface RF_huf_x4fin RF_huf_x4fin2 RF_huf_x4fin3 RF_huf_x4body_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x4fast () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZ_div_mod_eq_fullK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr07C56Stdlib6ZArith6BinInt1Z4to_NK46Stdlib;setoid_ring<Ring_polynom5PExpr09K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z:div_uniqueC47Corelib4Init5Logic6eq_symK46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z7div_divC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterK47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib;setoid_ring<Ring_polynom3Mon00I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z8mul_commC56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundC56Stdlib6ZArith6BinInt1Z7div_addC47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast:div5_magicC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast:div7_magicC4ELinuxProcessSemantics5Riscv7Prelude5bvmapI45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission3Lib5Image:ro_bytes_bC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib5Image>ro_cells_imageK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission3Lib4Step8ro_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells7cell_atC5ARocqVerifyHarness?AgentSubmission3Lib4Step=ro_cells_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib5Cells5csizeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells6cbytesK47Corelib4Init9Datatypes6option01C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission3Lib3ArrBnth_error_upd_sameC5ARocqVerifyHarness?AgentSubmission3Lib3ArrCnth_error_upd_otherC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_x4fin3X4MI47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions:bv_modulusC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiC45stdpp9bitvector;definitions6bv_addC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffI4ELinuxProcessSemantics5Riscv7Prelude4tree00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C56Stdlib6ZArith6BinInt1Z9add_assocC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:upd_lengthC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u64arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_writeC46Stdlib5Lists4List9nth_errorC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u64arr_readc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast6dbc_rdC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC35stdpp7tactics<f_equal_helpC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8load_u64C4ELinuxProcessSemantics5Riscv3Sem5alu64K4ELinuxProcessSemantics5Riscv5Instr5instr09C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_srliC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv7Prelude4zextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_srliC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init5Logic2or00C47Corelib4Init5Peano2ltC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin34WSOKK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fin39x4f_kloopC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K4ELinuxProcessSemantics5Riscv5Instr5instr08K4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_8'C5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeK46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission3Lib3MemDbytes_at_write_otherC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission3Lib4Step>rw_cells_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u64arr_frameC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame9stk_writeK4ELinuxProcessSemantics5Riscv5Instr5instr06C46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepI47Corelib4Init9Datatypes3nat00c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast3SPSI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K4ELinuxProcessSemantics5Riscv5Instr5aluop01C4ELinuxProcessSemantics5Riscv3Sem2w0C5ARocqVerifyHarness?AgentSubmission3Lib6MState6w0_litK47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize04I4ELinuxProcessSemantics5Riscv3Sem4core00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib7Numbers7BinNums1N01K4ELinuxProcessSemantics5Riscv5Instr5aluop07I47Corelib4Init5Peano2le00C47Corelib4Init5Logic8iff_reflK46Stdlib9micromega5Tauto8GFormula01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBbytes_at_transportC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC5ARocqVerifyHarness?AgentSubmission3Lib3Arr@u64arr_transportC5ARocqVerifyHarness?AgentSubmission3Lib5FrameFstk_transport_disjointC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6sub_fpC5ARocqVerifyHarness?AgentSubmission3Lib5Frame<munch_weakenC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_transC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_transC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKitAbytes_of_unsignedC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuK4ELinuxProcessSemantics5Riscv5Instr5instr05C56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib9micromega;ZifyClasses9and_morphC56Stdlib6ZArith6BinInt1Z6ltb_ltC56Stdlib6ZArith6BinInt1Z6ltb_geK4ELinuxProcessSemantics5Riscv5Instr5instr03C47Corelib4Init9Datatypes7nat_indC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega8ZifyInst7Inj_Z_ZC56Stdlib6ZArith4Znat5Nat2Z6inj_leC56Stdlib6ZArith4Znat5Nat2Z8inj_succK4ELinuxProcessSemantics5Riscv5Instr;branch_cond05C47Corelib4Init5Logic9False_indK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_subC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_subK4ELinuxProcessSemantics5Riscv5Instr5instr0BC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_mulhuC4ELinuxProcessSemantics5Riscv3Sem7mul_divC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7m_mulhuC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z7min_glbC56Stdlib6ZArith6BinInt1Z8le_min_lC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z:mul_div_leC56Stdlib6ZArith6BinInt1Z8le_min_rK4ELinuxProcessSemantics5Riscv5Instr5instr02C56Stdlib6ZArith6BinInt1Z6shiftlC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_auipcC5ARocqVerifyHarness?AgentSubmission3Lib4StepFunsigned_Z_to_bv_add_rC45stdpp9bitvector;definitions9bv_concatC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7b_auipcC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast5x4_wbC56Stdlib6ZArith6BinInt1Z7eqb_neqC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_slliC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_slliC56Stdlib6ZArith6BinInt1Z8max_specc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast8x4_innerC56Stdlib6ZArith6BinInt1Z?shiftl_mul_pow2C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_divc5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast6mulhu7c5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x4fast6mulhu5C5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK4ELinuxProcessSemantics5Riscv5Instr5aluop02K4ELinuxProcessSemantics5Riscv5Instr5mulop04K4ELinuxProcessSemantics5Riscv5Instr;branch_cond01K4ELinuxProcessSemantics5Riscv5Instr5aluop03".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Ltac u64_sok ARR i :=
  lazymatch type of ARR with u64arr ?segs ?mx ?A ?ws =>
    let a := cur_mem_addr in
    pose proof (u64arr_store_ok segs mx A ws i a ARR ltac:(rewrite ?upd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK
  end.
Ltac u64_store ARR i :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a (le8 ?v)) _) =>
    lazymatch type of ARR with u64arr ?segs mx ?A ?ws =>
      let E := addr_expr a in
      let ARR' := fresh "ARR" in
      assert (ARR' : u64arr segs (write_to_mem mx (wa E) (le8 v)) A (upd ws (Z.to_nat i) v));
      [ replace (wa E) with (wa (A + 8 * i)) by (unfold wa; f_equal; lia);
        apply (u64arr_write segs mx A ws i v ARR); rewrite ?upd_length; lia
      | clear ARR; store_done; rename ARR' into ARR ]
    end
  end.

(* [comment removed for export] *)
Lemma div5_magic : forall x, 0 <= x < 2^64 -> (x * 14757395258967641293 / 2^64) / 4 = x / 5.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fast ()) [] "h07__arithh14__ffh28__varmaph35__with42H0h52Hah64__p1h76__sat0h86__sat1h96__sat2h:6__sat3h;4__x1h<4__x2h=4__x3h>4__x4h?1ah@2zhhA5heq_qhB5heq_rhC1xhD1HhE2H1hF2H2hG2H3hH2H4hI4__p2hJ6__sat4hK6__sat5hL4__x5hM2HqhN2HrhO2HxhP7fv_listhQ8hyp_listhR3lmphS1qhT1rhU1zp%0p&0p;1p;2p;3p;4p;6p;7p;5p;8p;:p;<g0000j10Tg000Uj1;Tg0013j2iTg001Pj22Tg001lj27Tg002Gj19Tg002lR0j25Tg003Ij26Tg003fj28Tg004Fk20ETg004mj2?Tg005Gj1UTg005gj1MTg006Gk10<Tg006ek10;Tg007Ck103Tg007nj2GTg008Qj2yTg0093j2xTg009_j3JTg00:9j3uTg00:Xj4tTg00;Jj3rk20JTg00<1R1j2CTg00<Nj2VTg00<jj2lTg00=[j2kTg00>Lj2[Tg00?4j3ZTg00?Xj2jTg00@9k10KTg00@Rk20ITg00A9k20HTg00A_k20GTg00BEk20DTg00CAj2hTg00Cbj1@Tg00DAj1gTg00D_j2fTg00E@j3dTg00Eij2cTg00FRj2bTg00G>k20ATg00Gjj3LTg00HJj2TTg00Hhj4HTg00IFj2FTg00Iik10:Tg00JKj3RTg00Jnk302Tg00KQj1`Tg00Koj3_Tg00LRk301Tg00M5j6QTg00MSj2^Tg00N<j3PTg00Nej4zTg00O@j3|Tg00OZj1}Tg00PDj2OTg00Pdj2\Tg00QNj2]Tg00R8j3NTg00Rbj1wTg00S@j3vTg00Sjk304Tg00TTk305Tg00U>k107Tg00Ufk408Tg00VLk709Tg00W;j6qTg00W_k40=Tg00X;k60>Tg00X_k50?Tg00Y@R2k20@Tg00Y]j4XTg00ZHj7oTg00Zlk30BTg00[Uk60CTg00\9j7nTg00\]j8WTg00]Al:mTg00^2m<0FTg00^_R3f0R4'Vp=1%04#0p=e%04#0#9#9p={%04#0#9#9#0#0#9#9p=>%04#9p=sg00_=R5f1R6;J4p=4f2R7/5600@4p=<P5P6g00_[P4CXp=DP6g00`BR8g00`aR9P9g00aAR:P4g00aaFop=3%94#0p=pAJ543p=Y1c54p=AB0B564p=:P5P6g00bAP4CXp=EP6P8P9P9P:P4J0Cp=SP7P8P9P9P:P6P4Fnp=If6R;P8P9P9P:f5R<f4R=f3R>P8P9P9P:P7P6P4GWGWp=BP5P6g00bhP4CXp=KP>P8P9P9P:P7P6P4GWp>00%04#0#0#0p=~%04#0#0#0#0#0#0#0p==P5P3P6P2P0P1g00cOR?g00clR@g00dIRAP4M:mp>06P5P3P7P2P0P1P?P@PAg00djS00P6P4N<0Fp=a%14g00eYRA#0R?#;R1%0?R0#eR2#eRB#;RC'iRD,24'7P5%9ARE#{#>#>#>#>#>#>#>#sRF#;RG,56RH%;0RI,5D'6%9?RJ#;RK,67,44XU5166KP5187KP520E>KA<K64,4>RLePL18=KRL,?5146LRLePL16<KRL,?514>LRLePLg00f>RL#URM%MLRN&0<5RO&0;5RP&035RQ1G53RR1G5KRS'D'31yQ:RTP4P7g00fjRUg00gJRV'?S011x47=JUVdAu536CtRWb1b2b3123KRXP4b0bAbB9r=K%16126K'7RYePYP5P>15<GRY%p2R2#;RZ,i1R['6PYP[P>15>[,CYR\%1\R]12\[R^'712[\1V\3'7P]P^P5A<K>7S02154G15=[R^'CR]#1XC518<KR_,?5147_R_eS03P_16;KR`,?514=`R`eS04P`f7Ra/lKS05%1aRb%1KRcf9Rd/8K#1[[S06f8Re/kKS07%1ef:Rf/6K#1\c[S081[1CS091231Rg%1C123D[Rh[S0:%11Rig00gjRjAZ1C6UW5S0;%1DRC\j^5iS0<1[1ZS0=%1Z123[[Rk\gS0>AZ1Z6VjX5iS0?%1[Rl\j^5iS0@f=/jKS0A%YKRm$0Kf>Rn16nK18nK5<K'4[S0B20JnKS0Cf?Ro/8KRp#112pK'7\XS0D20IoKS0E12K3f@Rp/8KRq,2K1Vq3'7[S0F20HpKS0GfARq/6K#Y\mS0H20GqKS0IfBRr/8K/4r\mS0Jg00hFS0K20DrKRmeS0LPmP=g00hbRs1h3K'?PXeO1S0MfC/8KRX#112XK'7RXP6PjPdP4P6O2X?iRdPl^?iRlPf1h31,?sPgeRgO1RsPkP=PjPnP4P6O2X?iRnPC^?iRiPoPgO1RgPhp-0Rog00iHRC#@Rt#@Ru#@Rv#@Rw#ARx%gA,f5%Av5d5Rv%gF,f5%Au5d51c5CRC':':':%@wRw#@#A,:Cg00igRu'b+0A=LLMPNP5P51T5=P7POCHRFP6P51T5<P>POCHCHPPPQ1F50R0,ER,3Q1SQa5IQ&0:9RyPQPQ1F5ERE,ER,3QRzPyPQ1ERS,3QPy1F5JRJ,ER,3QFBPyPQ1F5AR{/KJ,3QPyPQ1F5?RJ/K0,3QR|PyPQ1SQe9IQzPyAR5S{>025JRJ1G5G5R51G51Re%`25_5R29R5{6015R{,ER,3QH00FBFBPTPWb1b2b3X;5X<5X=5X>5XL5X6oWI%1>R}/7<Pb\c\}147;14=;%1;/7fA<K<;/5G15<['C#1[[[[[^;5^<5^=5^>5^L5^6o^IoP4fKRf/2D18fKR}/2K16fKP}PffHRcfIRbPaPrfDfERrfJR~O<b0b:b9b@b8b7b@b4A<Kqp/5G15q['CRq#1ebHbGbFbEb4bDb7b8b9b:bJbKbAbBP<P6EQP5Q0212][XC5Q03P_Q04P`Q05Q06Q07Q08Q09Q0:Q0;Q0<Q0=Q0>Q0?Q0@Q0AQ0BQ0CQ0DQ0EQ0FQ0GQ0HQ0IQ0JQ0LPmQ0MPXP6PjPdPlPsPkP=PjPnPiPgPh%~B#=#=#=#=#=#=#=#;,^5Rh%Aw5P5AP5hx%At1^5K=P5C':,:v':':/bu=LLMPNP5PFP61T5>CHPPPQ1SQ;1D0S,3Q5IQPyPQP|PyPQ1KEJ,3QPyPQ%`B9_5eRe,DE,3Q9IQzPy1D{2,3QFBFBPTPWb1b2b3X;5X<5X=5X>5X6o12>K,7=147=A<K7>,4=%1<12<D'7A<K=</5G/C^/2[[[[[^;5^<5^=5^>5^6oP4%1}P}PfPcPbPaPrfGP~O9b0b:b9b@b8b7b@b412q[ebHbGbFbEb4bDb7b8b9b:bJbKbAbBP<P6EQCz3|%}5R</O<R<#U%M<%U59L5=9L5;%M5Q00P4P61\5A1]5G5N5RG1]51%wZ5v5RZ1\5?R?5N5AN5?Z:045G6055R?Q0KQ01%;ARA0066g00jS,O5&075'O#MP5P@AaA4GAaA4?H08bR=JUVdK09bPbQA<[>\,4YeEqH0=bNbMbTbS16HD/6IPHPDPIPMPNPOPPPQP8P9P9P:1KeR,3QJ0>PTPWb1b2b3%YDg00k;[P4b0PMPNPOPP1G5I,DR,3QPTPWb1b2b3123IP4b0I0?EQWOXC5o"). Qed.

Lemma div7_magic : forall x, 0 <= x < 2^64 ->
  ((x - x * 2635249153387078803 / 2^64) / 2 + x * 2635249153387078803 / 2^64) / 4 = x / 7.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fast ()) [] "h05heq_th17__arithh24__ffh34__p1h48__varmaph55__with64__x1h71zh82H0h93H12h:3H18h;2H6h<4__p2h=4__p3h>6__sat4h?6__sat5h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE1HhF5heq_qhG5heq_rhH2H1hI3H10hJ3H11hK3H13hL3H14hM3H15hN3H16hO3H17hP3H19hQ2H2hR3H20hS3H21hT3H22hU2H3hV2H4hW2H5hX2H7hY2H8hZ2H9h[2Hah\6__sat2h]6__sat3h^6__sat6h_6__sat7h`6__sat8ha6__sat9hb5__x10hc4__x7hd4__x8he4__x9hf1ahg7fv_listhh8hyp_listhi3lmphj2zhhk2E1hl2Hmhm2Hqhn2Hrho2Hthp2Hxhq2T0hr1qhs1rht1thu1xp%0p%1p&0p;1p;2p;6p;3p;4p;5p;7p;8p;:p;<g0000j10Tg000Uj1=Tg0013k20aTg002Gj1?Tg002lR0j22Tg003Ij21Tg003fj23Tg004Fk208Tg00kXk20YTg00M5j6iTg005Gj1yTg005gj1eTg006Gk10STg006ek10PTg007Ck10OTg007nj2VTg00KQk10JTg00Kok30GTg008Qk20DTg004mj2YTg0093k20CTg00:9k30@Tg00:Xk40?Tg001Pj27Tg00;Jj3|j2lTg00<Nj2NTg00Eik20:Tg00Cbj18Tg00FRj2^Tg00G>j2XTg00IFk206Tg00Iik10XTg001lj2HTg00l:k40WTg00l[k50VTg00Nek404Tg00OZk10TTg00PDj2xTg00Gjj3]Tg00Pdj2wTg00Sjk303Tg00QNk202Tg00R8j3vTg00TTj3uTg00U>k10QTg00Ufk400Tg00VLj7~Tg00<1R1j29Tg00Y@R2j25Tg00X;k60NTg00mGk40MTg00mhk60ITg00<jj2}Tg00=[j2dTg00>Lk20FTg00?4k30ETg00?Xj2cTg00@9j1rTg00@Rj2bTg00A9j2jTg00A_j2kTg00BEj2_Tg00CAj2pTg00DAj1RTg00Jnj3aTg00LRk30HTg00O@k30>Tg00W;k60KTg00W_k40LTg00X_k50=Tg009_j3[Tg00Y]j4sTg00ZHk701Tg00Zlj3mTg00HJk20<Tg00[Uk60;Tg00\9k705Tg00JKk30UTg00\]j8nTg00]Am:0_Tg00^2m<0^Tg00D_k20]Tg00E@k30\Tg00MSk20[Tg00N<k309Tg00Hhk40ZTg00^_R3f0R4'Np=4%04#0p=of2R5f1R6/74'Hp={%04#?#0#0p=\%?4#0#0#?p=Z%04#0#?#0p=`g00_=R715647[5p>0`f3R81256/545[7p=>1Y74p=BA[764p=6P7P6g00_[P4Csp=PP6g00`BR9g00`aR:P:g00aAR;P4g00aaR<K01p=;g00fjR=g00gJR>7[4p=q1N351764'Hp=A20:74p=:Am764p>07g00f>R??]64p=W20<74p=MP5P9P:P:P;P7P6g00bAP4CsP<K01p=<P6P9P:P:P;P4J0;p=OP5P9P:P:P;P6P4K05p=hB0U764p=UP8P9P:P:P;P5P6P4Gnp=z1N36/H4p=gP7P3P6P2P0P1g00cOR<g00clR@g00dIRAP4N:0_p>0RP7P3P5P2P0P1P<P@PAg00djS00P6P4N<0^p=tP7P6g00bhP4Csp=QA[743p=J1N64,H5p=L20]74p=SB0\764p=G20[74p=FB09756=m74p=IAm7649m75p=E%04#?p>0BB09764p=f%04#0#0#0#0#0#0#0p>0A%04#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=KP7P5P6P4H0Zp=@20674p=Cf6RAP9P:P:P;f5R<f4R1P8P9P:P:P;P5P6P4GnGnp=DP<P9P:P:P;P1P9P:P:P;P8P5K05P6P4Gnp=T%44R0g00eYR2#0RB#=RC%0BRD#0RE#0#oRF#=RG+0aRH7{4%?DS01#0#\#Z#`#\#Z#`#\#Z#`#\#Z#`#\#ZRI#?#=RJ,26RK/1HP7P7125JRL/1HRM,2H128JRN13NHRO80`4X77208LH12MH20YMHEiPLP4PH13LHC>RLePL11NHRL#B166LRLePL%y?RL%e?R?&0S7RM&0P7RP&0O7RQ1V73RR1V7CRS&0JF60G7RT'P';20DQ;RUP4P51Y=>S0220C45#qdB0@736H0?R>b2b4b5173HR=P4b1RVb09|NHAAOOH121JRO/1HRN#41NN1POPH%BN165NRNeRWPNp-0RXg00iHRY-0:7RZ%8YS03#8RY#:S04-07Zg00igR['^'X/WLR\P?%M6R]PPPQ20672R^9<QRR_1OQ85hQR`&0X:Ra1V7J,U^Rb9<QRS05CzPUP>b2b4b5X67W31H06R0%4K[^67^3XP417AHS06PAP<O3Rcb1b0PWPNPVb0RVH0WPOPHP1PVPWPNP\P?P]PPPQP`Pa1UT^9<QbCzPUP>b2b4b5X67X3X12H6,NK\0^67^3XPcb1b0I0VH041N51,g5RcePc&0T7Rc/xcRc#yS07%ecS08%y79]71S099]7A%e7S0:Q00P4P61w72Rc1w7BR060372027C9v705u7RKAu7c0R0g00hFRcQ02%=2R`00R6S0;g00jS,x7&0Q7'x#eS0<P7P@At`4KAt`40S0=H00bi#qdF~bgbh19<8RK128C'515<8R]'6R\eP\P719A1R\121C'5RNf7RW/9</1C/5<RV114C'6X77P711\C/51RO16V4X77%BO11NCP\P1PC12AJ/1HR\#B161\S0>eS0?Q0>PLP?PMPPPQP9P:P:P;1QSR,;QJ0NS0@PUP>b2b4b5%JCR;g00k;[S0AP4b1b0S0BH0MEi15A1R:P4J0IbE11KC/5811]C'6P711:CS0C%=DR],14%?2RK#?R9#=R\,1WRN'6X77P712C],1:164NX7711A\P713W\P7f8RN008\PNP\P6P4C>RVePVf9RV13V\Rd#B166dRdePdf:Rd/1\Re#B168eReePef;Re/2JS0D/1HRf#B16VfRfePfPLP?PMPP1V7\Rf,PR,;QPUP>b2b4b5173\RgP4b1b0bFbG7|\AA66\RhePhP7P815dNRh%=ERi'1PhPiP8128i,9hRj%4jRk17jiRl'H17ij?Lj3PkPl13d\Rl#B165lS0EeS0FQ0E11e\Rl#B161lS0GeS0HQ0Gf<Rl/2J/1HRk#B16dkS0IeS0JQ0If=Rk/2JRm/}HS0K%4m%4HRmf?Rn/2J/3H#4[[S0Lf>Ro/2JRp/dHS0M%4pf@Rp/2J/1H#4\m[S0N1}n\S0O%4nS0P%4\RqfARr/3\#4[[S0Q1dp\S0R%4pfBRp/1\#4\q[S0S20FCGS0T173CRq%4GP=[S0U[S0V%4CRsg00gjRtB0ECG6UW[S0WPm\t^[sS0XfCRG/5rRr/dCS0Y%4rfERr/5G/1C#4\s[S0ZfDRu/9pRv/dCS0[%4vfFRv/9uRu/1CRw#4\s[S0\19rG/cCS0]%r;RGPuPCPw13uCC>[S0^1luCS0_fGRu/9rRr/3CRw?AwC\qS0`1brCS0a17C3RrfHRw/9vRv/3CRx,7C?Lx3[S0b1jvCS0cfIRv/9uRu/1C#J\;S0d1kuCS0efJRu/9wRx/3C/6x\;S0fPc1_xCS0geS0hQ0gfKRx/5v/cCS0ifLRy/5uRuPC11uC13uCC>\GS0j1luCS0kfMRu/5xRx/3CRG?AGC\qS0l1bxCS0mfNRx/5yRy/3CRG,7C?LG3\rS0n1jyCS0ofO/5uRu/1C#J\;S0p1kuCS0qfPRu/5xRx/3C/6x\;S0rPc1_xCS0seS0tQ0sfQS0u/c\S0v%J\Rx#rfRR;P\11;\13;\C>[S0w1l;\S0xfSR;/3\Ry?Ay\\gS0y1b;\S0z17\3fTR;/3\Ry,7\?Ly3[S0{1j;\S0|fUR;/1\#J\xS0}1k;\S0~fVR;/3\/6;\xS10Pc1_;\S11eS12Q11fW/2J/cHS13%JHRx#rfXS14/2JRyPH11yH13yHC>[S151lyHS16fYS17/2JRy/3HRr?ArH\=S181byHS1917H3fZS1:/2JRy/3HRr,7H?Lr3[S1;1jyHS1<f[Ry/2JRr/1H#J\xS1=1krHS1>f\S1?/2JRr/3H/6r\xS1@Pc1_rHS1AeS1BQ1AP1g00hbRr1p3H'YP=eO1S1Cf]R=/2J/3HRx?AxHS1DPe1p3\,YrPgeO1S1Ef^Rg/3\Rx?Ax\S1FPp1p3C,YrPqeRqO1S1Gf_/5=/3CRr?ArCS1HPvPqO1S1If`S1J/9g/3CRr?ArCS1KP1PtPuP4P6O2XfsS1LPm^fsS1MQ0uPqO1S1NQ0U%8YRY#8Rq#8Ru#8Rr#8Rp#8Rx#8RG#8Rz#8R{#8R|#:%R2#SR2%:{R{'G%Fi%:pRp;IZ3E207Z{%?BR{#=#FR}%8|#8#8R|#8#:R~%0I$0B#?RI#=#F%:|'f%R{#S%:GRG'G%RI#SRI%:xRx'G1GIp%:q%oF$0A#K#K#KRF#=#FQ04'f3E3E3E7IZ/^['X'XRq%FJ%RF#S/GG%:YRY,G25E~7IZ%:zRz%:rRr5EZ/^['X,XG%RB#S/Gx=EzY%:uRu9EZG/^['X/WL'W,Wq'WP?%MW%Md7@1%MV?@<M7@5%MN?@dM%MARq7@87@6PPPQPQ%CDRD9<QRRG1PDT,;QPaPQPQ%CERE9<QR1OQlPaPQPQ%0KRz#0#CR~9<QR1OQkPaPQPQQ0@Pa%CBRB9a7^R2%CzRz,US=a7~'Q,;QCzPaPQPQA<QR2PaPQA<QRSPaA<QRzFDPaPQPQQ05PaPQA<QRTPa%0{#CR{9<QRFDPaPQ1QB{,;QPaPQ%CKR{Q01#C'Q,;QPaPQ%C9Rz/QE,;QRSPaPQ1Uf{=a7z,Q^,;QRzPaPQA<QRBA<QB^R~5hQPaPQ1UBT=a7D,Qb,;QRbPaPQ1OQo9hQ_Pa1V7iRD,U{:0H72R29<QRFDFDFDFDFDETETETPUP>b2b4b5X67X@7XA7XB7XC7XD7Xc7Xd7Xe7Xb7X3XX<XX=X%48R{?{8H1gWe%4eRB/HkQ0A151<RIPCPNPkC>[%4I%4d\s[12<JRs#4Q0P\m[16Wo16Vo16koPVP\PePoC>ALBedQ0DPlPHPoC>1glw15ko12ni'9#4[[[[[[[[[[[[[^67^@7^A7^B7^C7^D7^c7^d7^e7^b7^3X^<X^=XP4feRn/7HfcRo,5nRk/3CRw/7C13n\RB/7\Pw12nJRJ/1H11n\PBP=11kC13JHRJPgPoPnPWPAP<PvQ0uP;Q14Q17Q1:Q1?Q1JfbRvfdRkOJb1b?b>bjb8b;b9b:15=y12;i'9R;#4ebTbSbRbPb:bObNbMbLbKb9bJbIbZbYbXb;bWbVbUbQbHb8bEb\b]b>b?b^b_b`bab0bFbGQ0FQ0EQ0HQ0GQ0JQ0IQ0KQ0LQ0MQ0NQ0OQ0QQ0RQ0SQ0TQ0VQ0WQ0XQ0YQ0ZQ0[Q0\Q0]Q0^Q0_Q0`Q0aQ0bQ0cQ0dQ0eQ0fQ0hQ0gQ0iQ0jQ0kQ0lQ0mQ0nQ0oQ0pQ0qQ0rQ0tQ0sQ0vQ0wQ0xQ0yQ0zQ0{Q0|Q0}Q0~Q10Q12Q11Q13Q15Q16Q18Q19Q1;Q1<Q1=Q1>Q1@Q1BQ1AQ1CQ1DQ1EQ1FQ1GQ1HQ1IQ1KP1PtQ1LQ1MQ1NQ0U%F\%0F#o#=#FRF%R9#S/GYQ03#:,f}%K9#K#K#K#=#F/fZ3E9IFu9IFr7Ip7Ix/^[/WLP?A@q1M?@5M%M<9@M87@6PPPQPQPG1OQNPaPQPQ1OQV1PEf,;QPaPQPSPaPQPzPaPQPQ1OQdP~PaPQPbPaPQ1P^T,;Q9hQ_Pa1P2D,;QFDETFDETETPUP>b2b4b5X67X@7XA7XB7XC7XD7X3XX<XX=X1H{AA{NA\16AWP8P\P<PWC>ALl<1PsPAPHPNC>Q06,gA15WN12Vi'9/7i[[[[[[[^67^@7^A7^B7^C7^D7^3X^<X^=XP4%4o%4B17JHPBP=PJPgPoPnPWPAQ1:Q1?Q1JPvPkO@b1b?b>bjb8b;b9b:17;iebTbSbRbPb:bObNbMbLbKb9bJbIbZbYbXb;bWbVbUbQbHb8bEb\b]b>b?b^b_b`bab0bFbGH0440>Q07Q08Q099]7V9]7eQ0:Q00P4P6P02027iR61w7KRK5v7Av7K6:03705u7R0PcQ02Q0;Q0<P7P@Q0=At`40H00bi#qdF~bgbhPhPiP8PjC>eJ0KH0LbnbmbsbrQ0C/1]P:PCP]Q0BQ0?Q0>PLP?PMPP1V7],PR,;QPUP>b2b4b5173]P4b1b0I0=EiPOP4EibkbqblbobtWpXu7o"). Qed.

(* [comment removed for export] *)
Lemma mulhu5 : forall x, 0 <= x < 2^64 ->
  ((x * 14757395258967641293) ≫ 64 mod 18446744073709551616) ≫ 2 = x / 5.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fast ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__p1h61zh71Bh82Hxh91xp;1p;2p;3p;6p;4p;5p;7p;8g0000j10Tg000Uj18Tg0013j2ITg001Pj27Tg001lj29Tg002Gj11Tg002lj2=Tg00nDj2DTg003fj2?Tg003Ij22Tg009_j3<Tg00Eij2HTg00Cbj1FTg00Zlj3ZTg00FRj2YTg00G>j2XTg005Gj1WTg00Gjj3VTg005gj1TTg00HJj2RTg006ej1QTg007Cj1PTg007nj2;Tg00IFj2OTg00[Uj6NTg00Iij1KTg00JKj3CTg008Qj2JTg004mj2STg0093j2iTg00:9j3hTg00:Xj4gTg006Gj1fTg00KQj1eTg00Koj3cTg00l:j4bTg00ndj5aTg00Nej4_Tg00oPj2^Tg010Sj3`Tg00M5j6ATg0116j3GTg00<Nj2]Tg00Y]j4ETg00ZHj7\Tg00\9j7dTg00\]j8[Tg00^_R0f0R1']p=4%01#0#0#0p=M%01#0#1#1p=U%01#0#1#1#0#0#1#1p=5%01#1p=L%01#0p=j%01#0#0#0#0#0#0#0p=6g00_=R2f1R3g00bAP1CEp=:P3g00`BR4g00`aR5P5g00aAR6P1g00aaF\p=3f2R7P4P5P5P6P3P1Fdp=>f3R8P4P5P5P6P7P3P1G[p=BP2P3g00_[P1CEp=@%41R9g00eYR:#0R;#8R<%0;#MR=#8R>'IR?,71R@'9RAP2%1:#U#5#5#5#5#5#5#5#L#8RB,=3RC/D>RD%j=#6#6#6#6#6#6#6#8RE'?RF1I<<RG'2%1;#8R;,27RH9<21X62P212C?RI1?1E/2G=<2HX62%4IRH17I?RIPCP?p-0RJg00f>RKg00iHRL,H2RM%FL#F,H29Z2Mg00ig'Y'X%WKRM3VRL%TKRK1R23RN%Q2RO%P2RP1;20RQ1O2:R:':,3PRRPPP4P5P5P6P8ENR45>P%K5R51;2B9C2:RS,:Q,3PCB1JP6R6P1P7g00fjRTg00gJRU'S1i17=<TUdAh203CgRUb1b2b3X42W51993%4C[^42^5JP1177?P7P3O3b0PMPK%f2R9PO1;2<RT%e=5c2R=,@Q,3PP6PUb1b2b3170?P1b0R0CbPCP?P?P0PLPKPNPOPP1@:=,3PR:9>P4P5AC2==,@S,3PCBP6PUb1b2b3X42X5J193@1=??,7C[^42^5JP1%47P7P3O3b0DaC_19HIP21=7B/2?RI121G128;5<2X62PMPKPNPOPPA>PR:R:P5P:CBP6PUb1b2b3X42R:%43173?'9\A^42RAP1P8P7O2b0,^71?IEP:PAP11=8B/2?P3O2b09`IEEAb7PDPMPKP9PO1;2>,:Q,3PP6PUb1b2b3%4>P1b09GC>EA1DF<PMPKP9PO1:QT,3PP6PUb1b2b3%4<P1b09GF<EAW8X92o"). Qed.

Lemma mulhu7 : forall x, 0 <= x < 2^64 ->
  ((((x - (x * 2635249153387078803) ≫ 64 mod 18446744073709551616) mod 18446744073709551616) ≫ 1
     + (x * 2635249153387078803) ≫ 64) mod 18446744073709551616) ≫ 2 = x / 7.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x4fast ()) [] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with64__x2h75heq_th81zh94__x3h:1Hh;2Hah<4__p2h=6__sat3h>4__x4h?2Hxh@2T0hA6__sat1hB6__sat2hC6__sat4hD1thE1xp;1p;2p;3p;4p;5p;7p;6p;8g0000j10Tg000Uj1>Tg0013j2ZTg001Pj26Tg001lj24Tg002Gj1;Tg002lj2:Tg00nDj2STg003fj25Tg00<1j27Tg00Y@j2=Tg003Ij21Tg00<Nj29Tg004mj2HTg00Eij2ATg00Cbj1LTg00FRj2PTg00G>j2[Tg005Gj1gTg00Gjj3ITg005gj1fTg00HJj2OTg006ej1dTg007Cj1cTg007nj2DTg00IFj2MTg00Iij1bTg00JKj3TTg008Qj2~Tg0093j2|Tg009_j3aTg00:9j3{Tg00:Xj4zTg006Gj1yTg00KQj1xTg00Koj3vTg00l:j4uj2sTg00l[j5`Tg00Nej4_Tg011_j2tTg00=[j2^Tg00>Lj2rTg00?4j3qTg00CAj2pTg00DAj1oTg00D_j2nTg00E@j3mTg00Hhj4QTg00LRj3]Tg00Y]j4VTg00Jnj3jTg010Sj3UTg0116j3WTg00Zlj3iTg00ZHj7XTg00[Uj6wTg00\9j7\Tg00\]j8RTg00M5j6hTg00^_R0f0R1'9p=2%01#0#0#0p=e%;1#0p=l%01#;#0#0p=K%;1#0#0#;p=G%01#0#;#0p=N%01#0p=}%01#0#0#0#0#0#0#0p=@g00_=R2f1R3;a1p=8Ai231p=?f2R4g00`BR5g00`aR6P6g00aAR7P2P3g00bAP1CVg00aaR8FXp=3P3P5P6P6P7P1Ewp=FP4P5P6P6P7P3P1F\p=Bf3R9P5P6P6P7P4P3P1GRp=YP4P5P6P6P7P2P3g00_[P1CVP8FXp=<f6R:P5P6P6P7f5R;f4R<P9P5P6P6P7P4P3P1GRGRp=JP3P5P6P6P7P1P8FXp=kP;P5P6P6P7P<P5P6P6P7P9P4F\P3P1GRp=CP2P<P9P4P3P1Ehp=E%21R5g00eYR8#0R=#>R>%0=R?#eR@#>RA'ZRB,61'4RC%l?#K#G#N#K#G#N#K#G#N#K#G#N#K#G#;#>RD,:3RE/SARF%}@#@#@#@#@#@#@#@#>RG'5,73/5GRH%>8RI'SRJ/=F/5GRK1Z>>RL'1%;8RM#;#>RN,14RO,81X821Z>IRP,1H1:4DRQ/SA,=1/5G/1L/8OX8211EBRR151G,74/5G/1P/=1/5G/1L/8OX82PRP211QBRR#219R4PQPB1H2R181RRReROPRp-0RSg00f>RTg00iHRU,A2RV%LURU#LRW,A2RX,?Vg00igRY'PRZ'[%gTR[3IR\%fTR]1O23R^%d2R_%c2R`1D20Ra1M28Rb53`Rc1F`95B`Rd%b6R61D2DRe9T2bRf93`aCY1~`7R7P1P4g00fjRgg00gJRh'H1|14=aghdA{203CzRhb3b4b5X02W11453Rg%2E[^02^1SP116<BP<P9O3Rib2b7POPRP[P]%y2RjP_1D2>Rk%x@5v2R@9<`aP7Phb3b4b5160BRlP1b2b7RmCuPQPBP4PmPOPRP\P]P^P_P`PdP6AT2@b93`fCYP7Phb3b4b5X02X1S1:B3,9E\g^02^1SPib2b7D`C_1914,45RiePiP317<1/5G/1P/=4/5G/1L11<NRi'8X821793Rg111P/=4/5G/1L/8iX8211g>RL/=3RP%>?Rf,11/8iX821:9DRi/1BRd,H2183dRdeR\PdP[P]P^P_P`A<`b@R^9B`cRRP6PRCYP7Phb3b4b5X02%23RR163BRO'4\C^02P1P;P<O2b2b7,t911Pf119N'8e15PG%2P16PG1sg>%2g160>RN17;9/1>#2[[1:<D/1BRf,H2184fRfeRCPf1:;DRm/^B%2m%2BRmf7RQ/:D/1B#2[[1r>A%2ARnPl[Rl\N%2>Rog00gjRpAq>A3UW;Pm\p^;of8Rp/7:Rq/^>%2qf:Rq/7p/1>#2\o[P4g00hb1p0>'HPNeO1Pl%LWRW#LRl#L,A21A2lRl%o8,n21A2WRW5m2/?V'?'?/PY1[lZ=IT[5ITP]P2P21O2<P4PjCQP31O29RlCQP_P`P`1M2MRM1M2=R=5]2RZ93`aP6P`A3`akR8P6PcFJP6P`P`AT2Me93`aP6P`A3`a@P61M2?R?93`aFJP6P`P2P=g00bhP?CV,k`P6P`1F`:A3`=M5B`P6P`P`A3`aM1F`QP6Aj2b=R?93`aECFJFJP7Phb3b4b5X02X62X92X>2X1SX<S1743Re#2%24R0\o[%2i%2:Ri\m[189;19<;,4Qf9RQ,4i1=;:#2[[[[[^02^62^92^>2^1S^<SP1f;Rm/6B%2Q1:mD/1BPmPQ17mQ/1>P4P;P:PpPqO;b2b=bAbBb=bCb7b:PgP>PgP\PdP[P]PjP_A<`akP7Phb3b4b5PNP1b2b7P\PdP[P]P21O24RNP3PjCQRqP_P`P`1F`<RpA3`=bRmP6A]2b=RQAT2kQ53`ECP7Phb3b4b5X02X62X1S1931Rk,441734RD1:>D'9[^02^62^1SP1%29P9P;P4O4b2b7D`19LgPCPf1A2U/?VRV,?X/PY=IT[RXP]P2PNP3PlCQP_P`A3`bZP6P`1F`;A<`M@5B`P61D2GRM9<`?FJP7Phb3b4b5X02X62X92X1S191e169B,4<1=49/6G[[^02^62^92^1SP1PiP:P<17:</1>P4P;O6b2b7b:C_9UPGDE15gGP\Pd1?WV/PY=IT[P]PqP_P`P`A3`a=PmP6P`P`PpP^P6A3`aQA<`QM5B`ECECP7Phb3b4b5X02X62X1S14Rk149O1749RO#216OG'4[[^02^62^1SP1%2;ROP9P;P4P<O5b2b79UgGDE153GP\PdPXP]PqP_P`P`PcA3`b=P6P`P`PpA<`=@P6A<`bM9B`cECECP7Phb3b4b5X02X62X1S1913,45164B,49164G,40[[^02^62^1SP1POP;P9P4P<O5b2b79U3GDEb@bDPFP[P]PjP_1D2A93`aP7Phb3b4b5PnP1b29WEADEPJP[P]PjP_1D2I93`aP7Phb3b4b5%2IP1b29WHIDE1SK>P[P]PjP_P8P7Phb3b4b5PoP1b29WK>DEW?XE2o"). Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X4FAST.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT lo : Z) (src : list Z) (cells : list deltX1) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x1_table_ok cells 11.
  Hypothesis ECB : cbs = firstn 4096 (x1_bytes' cells).
  Hypothesis LCB : zlen cbs = 4096.
  Hypothesis D8 : 8 <= DST.
  Hypothesis DC : 0 < dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4096 <= lo.
  Hypothesis DJ1 : DT + 4 + 4096 <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.

  Notation DW := [(SP - 4096, SP); (DST, DST + dcap)].
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation FRS := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Notation X4M := (RF_huf_x4fin.X4M ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs).
  Notation XF l := (l ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 DST dcap SS DT lo src cells cbs
                     TOK ECB LCB D8 DC DL S0 SL NSM BYS DT0 CBL DJ1 DJ3 LOS SP16 SP47) (only parsing).

  Hypothesis BODY : x4_body_stmt.

  (* [comment removed for export] *)
  Notation HS pc mm x8 x9 a4 a5 x18 x19 x20 x22 x25 x26 x27 :=
    (MS (mkR (Z_to_bv 64 (SP - 184)) (Z_to_bv 64 (SP - 512)) gp tp (Z_to_bv 64 (-16)) (Z_to_bv 64 (SP - 224))
             (Z_to_bv 64 (-25)) x8 x9 (Z_to_bv 64 0x104e0) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 0xffc8)
             (Z_to_bv 64 (- (DT + 4) - 1)) a4 a5 (Z_to_bv 64 (SP - 144)) (Z_to_bv 64 (-17)) x18 x19 x20
             (Z_to_bv 64 (DT + 4)) x22 (Z_to_bv 64 5) (Z_to_bv 64 6) x25 x26 x27
             (Z_to_bv 64 (-24)) (Z_to_bv 64 2) (Z_to_bv 64 3) (Z_to_bv 64 4))
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition SPS : list word :=
    [Z_to_bv 64 0xcccccccccccccccd; Z_to_bv 64 0x2492492492492493; Z_to_bv 64 (DST + dcap); Z_to_bv 64 SS;
     Z_to_bv 64 DT; Z_to_bv 64 n; Z_to_bv 64 dcap; Z_to_bv 64 DST; Z_to_bv 64 SS; Z_to_bv 64 (DST + dcap)].

  Notation FAOK fa OP0 OP1 OP2 OP3 IP0 IP1 IP2 IP3 b0 b1 b2 b3 :=
    (nth_error fa 0 = Some (Z_to_bv 64 OP0) /\ nth_error fa 1 = Some (Z_to_bv 64 OP1)
     /\ nth_error fa 2 = Some (Z_to_bv 64 OP2) /\ nth_error fa 3 = Some (Z_to_bv 64 OP3)
     /\ nth_error fa 5 = Some (Z_to_bv 64 IP0) /\ nth_error fa 6 = Some (Z_to_bv 64 IP1)
     /\ nth_error fa 7 = Some (Z_to_bv 64 IP2) /\ nth_error fa 8 = Some (Z_to_bv 64 IP3)
     /\ nth_error fa 10 = Some b0 /\ nth_error fa 11 = Some b1 /\ nth_error fa 12 = Some b2 /\ nth_error fa 13 = Some b3
     /\ bv_unsigned b0 mod 512 <> 0 /\ bv_unsigned b1 mod 512 <> 0
     /\ bv_unsigned b2 mod 512 <> 0 /\ bv_unsigned b3 mod 512 <> 0).

  Notation IEND ws := (forall i, 0 <= i < 4 -> exists ei, nth_error ws (Z.to_nat (15 + i)) = Some ei /\ 9 <= bv_unsigned ei).

  Ltac arr_lim A :=
    lazymatch A with
    | (bv_unsigned sp + -456) => constr:(80) | (bv_unsigned sp + -376) => constr:(152)
    | (bv_unsigned sp + -224) => constr:(120) | _ => constr:(0) end.
  Ltac arr_rd :=
    let E0 := cur_mem_addr in let E := addr_expr E0 in
    match goal with W : u64arr usegs ?mm ?A ?ws |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let k := addr_diff E A in let lim := arr_lim A in
      let ok := eval vm_compute in (Z.leb 0 k && Z.ltb k lim && Z.eqb (Z.modulo k 8) 0)%bool in
      lazymatch ok with true =>
        let i := eval vm_compute in (k / 8) in
        pose proof (u64arr_read usegs mm A ws i _ _ W ltac:(first [reflexivity | eassumption]) ltac:(lia) ltac:(unfold wa; f_equal; lia))
      end end.
  Ltac arr_st :=
    let E0 := cur_mem_addr in let E := addr_expr E0 in
    match goal with W : u64arr usegs ?mm ?A ?ws |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let k := addr_diff E A in let lim := arr_lim A in
      let ok := eval vm_compute in (Z.leb 0 k && Z.ltb k lim && Z.eqb (Z.modulo k 8) 0)%bool in
      lazymatch ok with true =>
        let i := eval vm_compute in (k / 8) in
        u64_sok W i; zstep; u64_store W i
      end end.
  Ltac wb_to pc :=
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
            | _ => first [zstep | (arr_rd; zstep) | arr_st] end).

  Ltac zl := repeat match goal with |- context [Z.of_nat (length ?l)] => change (Z.of_nat (length l)) with (zlen l) end.

  Ltac ltb_simp := repeat match goal with |- context [Z.ltb ?a ?b] =>
    first [ replace (Z.ltb a b) with true by (symmetry; apply Z.ltb_lt; lia)
          | replace (Z.ltb a b) with false by (symmetry; apply Z.ltb_ge; lia) ] end.
  Ltac lit_eval := repeat match goal with
    | |- context [Z.b2z ?x] => let v := eval vm_compute in (Z.b2z x) in is_Zlit v; change (Z.b2z x) with v
    | |- context [Z.lxor ?x ?y] => let v := eval vm_compute in (Z.lxor x y) in is_Zlit v; change (Z.lxor x y) with v
    end.
  Ltac cond_solve :=
    unfold bv_ltu, bv_leu, bv_eqb; rewrite ?Z.shiftl_mul_pow2 by lia; ltb_simp; lit_eval;
    rewrite ?unsigned_lit by lia; solve_cond_rec.
  Ltac cond_by :=
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
      let C := fresh "C" in
      first [ assert (C : c = true) by cond_solve; replace (if c then a else b) with a by (rewrite C; reflexivity)
            | assert (C : c = false) by cond_solve; replace (if c then a else b) with b by (rewrite C; reflexivity) ];
      clear C
    end.

  Ltac ucond C := unfold bv_ltu, bv_leu, bv_eqb in C; rewrite ?Z.shiftl_mul_pow2 in C by lia;
    rewrite ?unsigned_lit in C by lia; zify_bool C.
  Tactic Notation "if_split" ident(C) :=
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
      destruct (Bool.bool_dec c true) as [C|C];
      [ replace (if c then a else b) with a by (rewrite C; reflexivity)
      | apply Bool.not_true_is_false in C; replace (if c then a else b) with b by (rewrite C; reflexivity) ]
    end.

  Ltac ob_to :=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
            | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18384) _ _ _ _) => fail
            | |- evt _ _ (MS _ _ (Z_to_bv 64 0x17338) _ _ _ _) => fail
            | _ => first [zstep | (arr_rd; zstep)] end).
  Lemma x4m_body : forall mm mm' sps ws fa fa',
    X4M mm sps ws fa ->
    munch [(DST, DST + dcap); (SP - 224, SP - 104)] mm mm' -> wmono usegs mm mm' -> mem_inv usegs mm' ->
    (exists obuf', u8arr usegs mm' DST obuf' /\ Z.of_nat (length obuf') = dcap) ->
    u64arr usegs mm' (SP - 224) fa' -> length fa' = 15%nat ->
    X4M mm' sps ws fa'.
  Proof using All.
    intros mm mm' sps ws fa fa' X MU' WM' MI' [ob [OB LOB]] FA' LFA'.
    destruct X as (BUF & SRCB & CBSB & STK & [j0 J0] & SPSA & LSPS & WSA & LWS & FAA & LFA & FR & MI & MU & WM).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (LCB' : Z.of_nat (length cbs) = 4096) by exact LCB.
    unfold RF_huf_x4fin.X4M.
    split; [exists (map bv_unsigned ob); split;
            [ rewrite map_map; erewrite map_ext by (intros; apply byte_of_unsigned); rewrite map_id; exact OB
            | change (zlen (map bv_unsigned ob)) with (Z.of_nat (length (map bv_unsigned ob))); rewrite length_map; exact LOB ]|].
    split; [eapply bytes_at_transport; [exact SRCB| exact MU'| rewrite length_map; zl; cbn [disjoint_from]; lia]|].
    split; [eapply bytes_at_transport; [exact CBSB| exact MU'| cbn [disjoint_from]; lia]|].
    split; [eapply stk_transport_disjoint; [exact STK| exact MU'| exact WM'| cbn [disjoint_from]; lia]|].
    split; [exists j0; eapply rw_cells_transport; [exact J0| exact MU'| exact WM'| cbn; lia]|].
    split; [eapply u64arr_transport; [exact SPSA| exact MU'| exact WM'| rewrite LSPS; cbn [disjoint_from]; lia]|].
    split; [exact LSPS|].
    split; [eapply u64arr_transport; [exact WSA| exact MU'| exact WM'| rewrite LWS; cbn [disjoint_from]; lia]|].
    split; [exact LWS|].
    split; [exact FA'|].
    split; [exact LFA'|].
    split; [eapply rw_cells_transport; [exact FR| exact MU'| exact WM'| cbn; lia]|].
    split; [exact MI'|].
    split; [eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU']; unfold sub_fp; intros ?x; cbn; intuition lia]|].
    eapply wmono_trans; [exact WM| exact WM'].
  Qed.

  (* [comment removed for export] *)
  Lemma dbc_rd : forall m1, mem_inv usegs m1 ->
    ov_read_bytes usegs m1 (Z_to_bv 64 66704) 8 = Some (le8 (Z_to_bv 64 151050438420815295)).
Proof using All.
  intros m1 MI.
  assert (RC : ro_cells usegs m1 66704 [CB (length (le8 (Z_to_bv 64 151050438420815295))) (le8 (Z_to_bv 64 151050438420815295))])
    by (apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | cbn; lia]).
  exact (ro_cells_read_at usegs m1 _ _ 0 _ 8 _ RC eq_refl eq_refl eq_refl).
Qed.

  (* [comment removed for export] *)
  Lemma x4_wb : forall mm ws fa (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3
      (xra t0 t1 t2 x8 x9 a1 a3 a4 a5 a6 a7 x18 x19 x20 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word),
    X4M mm SPS ws fa -> FAOK fa OP0 OP1 OP2 OP3 IP0 IP1 IP2 IP3 b0 b1 b2 b3 ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) -> IEND ws ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= DST + dcap -> DST <= OP1 <= DST + dcap -> DST <= OP2 <= DST + dcap -> DST <= OP3 <= DST + dcap ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -512)) gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 0x104e0) a1 (Z_to_bv 64 0xffc8)
                           a3 a4 a5 a6 a7 x18 x19 x20 (Z_to_bv 64 (DT + 4)) x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17338) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros X FO W13 IE I0 I0' I1 I1' I2 I2' I3 I3' O0 O1 O2 O3.
    destruct X as ([buf [BUFA LBUF]] & SRCB & CBSB & STK & [j0 J0] & SPSA & LSPS & WSA & LWS & FAA & LFA & FR & MI & MU & WM).
    destruct FO as (F0 & F1 & F2 & F3 & F5 & F6 & F7 & F8 & F10 & F11 & F12 & F13 & M0 & M1 & M2 & M3).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (dbc_rd mm MI) as DBC.
    wb_to 0x173d4.
    rewrite zb_lxor_ones by lia.
    replace (Z_to_bv 64 (18446744073709551615 - (DT + 4))) with (Z_to_bv 64 (- DT - 5))
      by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn;
          replace (18446744073709551615 - (DT + 4)) with (- DT - 5 + 1 * 18446744073709551616) by lia;
          rewrite Z.mod_add by lia; reflexivity).
    rewrite (Z.shiftr_div_pow2 (dcap + 3) 2) by lia.
    do 19 (destruct ws as [|? ws]; [cbn in LWS; lia|]). destruct ws; [|cbn in LWS; lia].
    eapply ((XF x4f_kloop) 3%nat 0 DST); [lia | lia | | .. ].
    { unfold RF_huf_x4fin.X4M.
      split; [exists buf; split; [eassumption | exact LBUF]|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [exists j0; eassumption|].
      split; [eassumption|]. split; [rewrite ?upd_length; exact LSPS|].
      split; [eassumption|]. split; [reflexivity|].
      split; [eassumption|]. split; [exact LFA|].
      split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. eassumption. }
    all: try reflexivity.
    1: exact W13.
    2: lia.
    unfold RF_huf_x4fin3.WSOK. intros i Hi.
    assert (HI : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct (IE i ltac:(lia)) as [e [He1 He2]].
    destruct HI as [ -> | [ -> | [ -> | -> ] ] ].
    all: eexists _, _; split; [reflexivity|]; split; [reflexivity|].
    all: split; [lia|]; split; [lia|]; split; [lia|].
    all: split; [eexists; split; [reflexivity|]; intro Hz; rewrite Hz in *; cbn in *; contradiction|].
    all: exists e; split; [exact He1 | exact He2].
  Qed.

  (* [comment removed for export] *)
  Lemma x4_inner : forall (r : nat) mm ws fa (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3
                          (x9 a4 a5 x18 x19 x20 x22 x26 x27 : word),
    X4M mm SPS ws fa -> DT mod 2 = 0 -> FAOK fa OP0 OP1 OP2 OP3 IP0 IP1 IP2 IP3 b0 b1 b2 b3 ->
    (1 <= r)%nat -> OP3 + 5 * Z.of_nat r <= DST + dcap ->
    SS + 7 * Z.of_nat r <= IP0 -> IP0 + 8 <= SS + n -> SS + 7 * Z.of_nat r <= IP1 -> IP1 + 8 <= SS + n ->
    SS + 7 * Z.of_nat r <= IP2 -> IP2 + 8 <= SS + n -> SS + 7 * Z.of_nat r <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= OP3 -> DST <= OP1 <= OP3 -> DST <= OP2 <= OP3 -> DST <= OP3 ->
    (forall mm' fa' (b0' b1' b2' b3' : word) IP0' IP1' IP2' IP3' OP0' OP1' OP2' (x9' a5' x18' x19' x20' x22' x27' : word),
       X4M mm' SPS ws fa' -> FAOK fa' OP0' OP1' OP2' (OP3 + 5 * Z.of_nat r) IP0' IP1' IP2' IP3' b0' b1' b2' b3' ->
       SS <= IP0' -> IP0' + 8 <= SS + n -> SS <= IP1' -> IP1' + 8 <= SS + n ->
       SS <= IP2' -> IP2' + 8 <= SS + n -> SS <= IP3' -> IP3' + 8 <= SS + n ->
       DST <= OP0' <= OP3 + 5 * Z.of_nat r -> DST <= OP1' <= OP3 + 5 * Z.of_nat r -> DST <= OP2' <= OP3 + 5 * Z.of_nat r ->
       evt usegs POST (HS 0x182f0 mm' b0' x9' (Z_to_bv 64 (OP3 + 5 * Z.of_nat r)) a5' x18' x19' x20' x22'
                         (Z_to_bv 64 (OP3 + 5 * Z.of_nat r)) (Z_to_bv 64 IP0') x27')) ->
    evt usegs POST (HS 0x18384 mm b0 x9 a4 a5 x18 x19 x20 x22 (Z_to_bv 64 (OP3 + 5 * Z.of_nat r)) x26 x27).
  Proof using All.
    induction r as [|r IH];
      intros mm ws fa b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x9 a4 a5 x18 x19 x20 x22 x26 x27
        X DT2 FO R1 OB I0 I0' I1 I1' I2 I2' I3 I3' O0 O1 O2 O3 K; [lia|].
    pose proof X as X0.
    destruct X as ([buf [BUFA LBUF]] & SRCB & CBSB & STK & J0 & SPSA & LSPS & WSA & LWS & FAA & LFA & FR & MI & MU & WM).
    destruct FO as (F0 & F1 & F2 & F3 & F5 & F6 & F7 & F8 & F10 & F11 & F12 & F13 & M0 & M1 & M2 & M3).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (LCB' : Z.of_nat (length cbs) = 4096) by exact LCB.
    apply (BODY POST mm F fc gp tp (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (OP3 + 5 * Z.of_nat (S r))) b0 b1 b2 b3
             x9 a4 a5 x18 x19 x20 x22 x26 x27 SP (DT + 4) DST dcap SS n IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3
             (map (Z_to_bv 8) buf) cbs (map (Z_to_bv 8) src) cells fa);
      try assumption; rewrite ?length_map; zl; try lia.
    intros mm' fa' b0' b1' b2' b3' nb0 nb1 nb2 nb3 j9' j15' j18' j19' j20' j22' j27'
      MU' WM' MI' OB' FA' LFA' G0 G1 G2 G3 G5 G6 G7 G8 G10 G11 G12 G13 N0 N1 N2 N3 NB0 NB1 NB2 NB3.
    assert (X' : X4M mm' SPS ws fa').
    { eapply x4m_body; [exact X0| exact MU'| exact WM'| exact MI'| | exact FA'| exact LFA'].
      destruct OB' as [ob [OBA LOB]]. exists ob. split; [exact OBA|]. rewrite LOB, ?length_map. zl. lia. }
    clear MU' WM' MI' OB' FA' LFA'.
    zstep.
    destruct r as [|r].
    - cond_by. zto 0x182f0.
      eapply (K mm' fa' b0' b1' b2' b3' (IP0 - nb0) (IP1 - nb1) (IP2 - nb2) (IP3 - nb3) (OP0 + 5) (OP1 + 5) (OP2 + 5));
        [exact X' | repeat split; assumption | lia ..].
    - cond_by.
      assert (E : OP3 + 5 * Z.of_nat (S (S r)) = OP3 + 5 + 5 * Z.of_nat (S r)) by lia.
      rewrite E in K |- *.
      eapply (IH mm' ws fa' b0' b1' b2' b3' (IP0 - nb0) (IP1 - nb1) (IP2 - nb2) (IP3 - nb3) (OP0 + 5) (OP1 + 5) (OP2 + 5) (OP3 + 5));
        [exact X' | exact DT2 | repeat split; assumption | lia .. | ].
      intros. eapply K; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma x4_outer : forall (fuel : nat) mm ws fa (b0 b1 b2 b3 : word) IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3
                          (x8 x9 a5 x18 x19 x20 x22 x25 x27 : word),
    X4M mm SPS ws fa -> DT mod 2 = 0 -> FAOK fa OP0 OP1 OP2 OP3 IP0 IP1 IP2 IP3 b0 b1 b2 b3 ->
    nth_error ws 13 = Some (Z_to_bv 64 SS) -> IEND ws -> DST + dcap - OP3 < 5 * Z.of_nat fuel ->
    SS <= IP0 -> IP0 + 8 <= SS + n -> SS <= IP1 -> IP1 + 8 <= SS + n ->
    SS <= IP2 -> IP2 + 8 <= SS + n -> SS <= IP3 -> IP3 + 8 <= SS + n ->
    DST <= OP0 <= OP3 -> DST <= OP1 <= OP3 -> DST <= OP2 <= OP3 -> DST <= OP3 <= DST + dcap ->
    evt usegs POST (HS 0x182f0 mm x8 x9 (Z_to_bv 64 OP3) a5 x18 x19 x20 x22 x25 (Z_to_bv 64 IP0) x27).
  Proof using All.
    induction fuel as [|fuel IH];
      intros mm ws fa b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3 x8 x9 a5 x18 x19 x20 x22 x25 x27
        X DT2 FO W13 IE FU I0 I0' I1 I1' I2 I2' I3 I3' O0 O1 O2 O3; [lia|].
    pose proof X as X0. pose proof FO as FO0.
    destruct X as (BUF & SRCB & CBSB & STK & J0 & SPSA & LSPS & WSA & LWS & FAA & LFA & FR & MI & MU & WM).
    destruct FO as (F0 & F1 & F2 & F3 & F5 & F6 & F7 & F8 & F10 & F11 & F12 & F13 & M0 & M1 & M2 & M3).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold SPS in SPSA.
    change (SP - 512) with (SP + -512).
    ob_to.
    rewrite (mulhu5 (DST + dcap - OP3)) by lia.
    rewrite (mulhu7 (IP0 - SS)) by lia.
    if_split C1; ucond C1.
    all: repeat (ob_to; first [cond_by | let C := fresh "C" in if_split C; ucond C]).
    all: ob_to.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x17338) _ _ _ _) =>
             eapply x4_wb; [exact X0 | exact FO0 | exact W13 | exact IE | lia .. ]
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x18384) _ _ _ _) =>
             match goal with |- context [?o + ?q + ?q ≪ 2] =>
               replace (o + q + q ≪ 2) with (o + 5 * Z.of_nat (Z.to_nat q))
                 by (rewrite Z.shiftl_mul_pow2, Z2Nat.id by lia; lia);
               change (SP + -512) with (SP - 512);
               eapply (x4_inner (Z.to_nat q) mm ws fa b0 b1 b2 b3 IP0 IP1 IP2 IP3 OP0 OP1 OP2 OP3);
                 [exact X0 | exact DT2 | exact FO0 | lia .. | ];
               intros mm' fa' b0' b1' b2' b3' IP0' IP1' IP2' IP3' OP0' OP1' OP2' x9' a5' x18' x19' x20' x22' x27'
                 X' FO' J0' J0'' J1' J1'' J2' J2'' J3' J3'' P0' P1' P2';
               eapply IH; [exact X' | exact DT2 | exact FO' | exact W13 | exact IE | lia .. ]
             end
         end.
  Qed.

End X4FAST.
End CANSEC1.
