(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT
  HufPure_HufStats HufPure_HufStatsRT HufPure_HufX1 HufPure_HufTableX1 HufPure_HufTableX1RT HufPure_FseReadBridge.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun HufWalkKit FseRdKit2 WStr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_iface RF_huf_h_iface RF_huf_tbl_iface RF_huf_tbl_iface2
  RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_tk RF_huf_bdt_model RF_huf_rs_pure
  RF_huf_x1t_model RF_huf_x1t_cls RF_huf_x1t_wk RF_huf_x1t_top.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_x1t_rsc () := "C46Stdlib5Lists4List8nil_consC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List6nth_okC47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List8map_consC46Stdlib5Lists4List:firstn_nilI47Corelib4Init9Datatypes4list00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init9Datatypes3nat02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib7Numbers7BinNums8positive02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC47Corelib4Init5Peano2ltC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01K47Corelib4Init9Datatypes4list02C35stdpp7tactics<f_equal_helpC47Corelib4Init9Datatypes7nat_indC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C47Corelib5Lists7ListDef6firstnC47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib6ZArith4Znat5Nat2Z8inj_succK46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith4Znat5Nat2Z6inj_ltK47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z8eqb_specC56Stdlib6ZArith6BinInt1Z3eqbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z3b2zC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4landC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega5Tauto8GFormula07C47Corelib4Init5Logic6eq_symC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z9land_onesC56Stdlib6ZArith6BinInt1Z9land_commK47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_rs_fin<upd_app_mid'C46Stdlib5Lists4List:length_mapC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC46Stdlib5Lists4List9app_assocC46Stdlib5Lists4List7map_appc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_rsc@firstn_snoc_ZnthC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_rs_pure?skipn_Znth_consC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr3updC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z7inj_minI47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3subc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_rsc4rsw1I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;Forall_ZnthC47Corelib4Init3Nat3addC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC46Stdlib5Lists4List:length_appC46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C46Stdlib5Lists4List>nth_error_nth'C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib5Arith8PeanoNat3Nat7add_0_rC46Stdlib5Lists4List?nth_error_skipnI47Corelib4Init5Peano2le00C46Stdlib5Lists4List>nth_error_app2C46Stdlib5Lists4List=nth_error_mapC46Stdlib5Lists4List>nth_error_app1C5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib3Arr:u8arr_readC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3zxbK4ELinuxProcessSemantics5Riscv7Prelude4tree01K4ELinuxProcessSemantics5Riscv7Prelude4tree02C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00K4ELinuxProcessSemantics5Riscv5Instr5instr06C45stdpp9bitvector;definitions9bv_signedC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec6v_addiI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC45stdpp9bitvector;definitions:bv_extractC4ELinuxProcessSemantics5Riscv7Prelude4zextC45stdpp9bitvector;definitions6bv_addK4ELinuxProcessSemantics5Riscv3Sem4core01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C5ARocqVerifyHarness?AgentSubmission3Lib3MemAzext_extract_byteC56Stdlib6ZArith6BinInt1Z7add_0_rC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib4StepDunsigned_Z_to_bv_addC4ELinuxProcessSemantics5Riscv7Prelude4sextC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9b_addsextI4ELinuxProcessSemantics5Riscv7Prelude4tree00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_sltiuK4ELinuxProcessSemantics5Riscv5Instr5instr08C5ARocqVerifyHarness?AgentSubmission3Lib6MState;lit_add_litC4ELinuxProcessSemantics5Riscv3Sem5alu64C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec9alu_sltiuC45stdpp9bitvector;definitions7bv_wrapC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec8alu_addiK4ELinuxProcessSemantics5Riscv5Instr5instr0:C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_andC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec5v_addC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7alu_addC5ARocqVerifyHarness?AgentSubmission3Lib3Arr>u8arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le1C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK4ELinuxProcessSemantics5Riscv5Instr5instr07C4ELinuxProcessSemantics?LinuxProcessSem6BvBase=Z_to_le_bytesC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_1'K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z7mod_modC5ARocqVerifyHarness?AgentSubmission3Lib3Mem<Z_to_bv8_modC5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u8arr_writeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem=mem_inv_storeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame6insideC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;munch_writeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame;wmono_writec5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_rsc6rw_updC4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbK4ELinuxProcessSemantics5Riscv5Instr5instr05C5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge6zr_litC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridgeBinr64_unsigned_litC46Stdlib4Bool4Bool=negb_true_iffC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7eqb_neqC46Stdlib4Bool4Bool>negb_false_iffC56Stdlib6ZArith6BinInt1Z6eqb_eqC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit7le1_litc5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_x1t_rsc<rescale_byteC5ARocqVerifyHarness?AgentSubmission3Lib6MStateAunsigned_lit_wrapC5ARocqVerifyHarness?AgentSubmission3Lib7ZBridge;v_sltiu_b2zC5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_fdw_kit>unsigned_byte'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtK46Stdlib9micromega7EnvRing5PExpr04C47Corelib4Init9Datatypes:option_mapC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepC4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallC4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyC5ARocqVerifyHarness?AgentSubmission3Lib6MState8step_genC5ARocqVerifyHarness?AgentSubmission3Lib6MState;lift_resultC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission3Lib4Exec8evt_stepC5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leI4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics5Riscv3Sem4core00I4ELinuxProcessSemantics5Riscv5Instr5instr00K4ELinuxProcessSemantics5Riscv5Instr5msize01K47Corelib7Numbers7BinNums1N01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK4ELinuxProcessSemantics5Riscv5Instr5aluop05K4ELinuxProcessSemantics5Riscv5Instr5aluop01K4ELinuxProcessSemantics5Riscv5Instr5aluop0:K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01I47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission4SpecBHufPure_HufTableX1:shift_rankC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4loadC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_x1t_model<shift_rank_SC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model;bind_Ok_invI47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model7load_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount5storeC5ARocqVerifyHarness?AgentSubmission5Ubsan@RF_huf_bdt_model8store_OkC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZupdC45stdpp9bitvector;definitions5bv_eqI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr07K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1C56Stdlib6ZArith6BinInt1Z7mod_addC45stdpp9bitvector;definitions@Z_to_bv_unsignedC5ARocqVerifyHarness?AgentSubmission5Ubsan=RF_huf_x1t_fw=nth_map_Znth'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr;u32arr_readC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le4C5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32C5ARocqVerifyHarness?AgentSubmission3Lib3Mem@sext_extract_le4C45stdpp9bitvector;definitions8bv_swrapK4ELinuxProcessSemantics5Riscv5Instr5instr0;C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7v_addiwC4ELinuxProcessSemantics5Riscv3Sem5low32C4ELinuxProcessSemantics5Riscv3Sem5alu32C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7w_addiwC5ARocqVerifyHarness?AgentSubmission3Lib3Arr?u32arr_store_okC5ARocqVerifyHarness?AgentSubmission3Lib4Step>store_bytes_4'C5ARocqVerifyHarness?AgentSubmission3Lib3Arr<u32arr_writeK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le4K46Stdlib9micromega:ZMicromega;ZArithProof03C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount7upd_natC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkMem;map_upd_natC5ARocqVerifyHarness?AgentSubmission4Spec9FseLemmas>upd_nat_lengthC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_rs_cl>Forall_upd_natC4ELinuxProcessSemantics5Riscv7Prelude6bv_ltuC56Stdlib6ZArith6BinInt1Z6ltb_ltC57Corelib7BinNums6PosDef3Pos6to_natC47Corelib4Init5Logic7f_equalC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC5ARocqVerifyHarness?AgentSubmission6Common9FseRdKit2:sx32_smallC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u32arrC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterI47Corelib7Numbers7BinNums1N00K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00K4ELinuxProcessSemantics5Riscv5Instr5msize03K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition rsw1 (scale w : Z) : Z := if w =? 0 then w else to_byte (w + scale).

Lemma firstn_snoc_Znth : forall (l : list Z) k, 0 <= k < zlen l ->
  firstn (Z.to_nat (k + 1)) l = firstn (Z.to_nat k) l ++ [Znth k l].
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_rsc ()) [] "p'0h02Hkh14__p1h24__x1h34__x2h41li001lh51xh67__arithh74__ffh88__varmaph95__with:4__p2h;4__x3h<4cstrh=1nh>2H0h?3Hk0h@4__p3hA2z0hB1HhC2H1hD2IHhE5cstr0hF1khG1yhH2z1i011zp&0p;1p;2p;3p;<p;4p;8p;6p;7p10000p4p710g000MR0p4p710p8p1000ip4p710p1001Dp4p710R1p8p1001bp4p7210P1p8p1002?p4p710P1p8g002^R1j1hTg003>R2j13Tg003^R3j25Tg004:j22Tg004UR4j1JTg0055R5j10Tg005Tj1uTg0062j2;Tg006Oj3>j1lTg006ik20;Tg007Lk30:Tg007il<QTg008Nj1OTg0093j2WTg009Uj2BTg009oj2HTg00:Xj1rTg00;6j2qTg00;Wj3gTg00<@j1cTg00<`j2UTg00=>j4bTg00=\j1nTg00>:j1mTg00>ej2TTg00?Hk10<Tg00?mj2iTg00@Pk109Tg00A2j3`Tg00AUk108Tg00B:k207Tg00B\j2MTg00C6k206Tg00Cbk305Tg00DAk404Tg00E3j4\Tg00E^j2eTg00FVR6j24Tg00Fnj4YTg00GUj1{Tg00H3j3Nj2yTg00HSj8wTg00I0j4vTP0j6tTg00IQj2jTg00Imj2|Tg00JMj2sTg00Jjl<fTg00KOj3~Tg00L8k200Tg00Ldk601Tg00MHj4]Tg00N3j7pTg00NWk702Tg00O;k703Tg00O_j8oTg00PCj3_Tg00Pbj3kTg00Q?j4dTg00Q[R0f0R7'jp=?g00R9R8/|7p=:1s07p=7f1R9=>87p=<1M87p=@P8g00RWR:P8P8P4f4R4P2f3R;g00S6f2R<P9P7M<fp=^P:P:P8P8P5P2P2P;g00ScP<P9P7M<fp=P1507p=D1j70p=EA>870p=KA~897p=6g00TG-007p=Cg00U3R5?N97p=GP9g00U_R=g00V>R>P>g00V^R?P7J01p=IP8P9g00W>P7C]p=SP9P=P>P>P?P7g00WeFpp=1P<P=P>P>P?P9P7K02p=AP8P9g00XEP7C]p=RP<P=P>P>P?P9P7K03p=aP8P9g00XlP7C]p=FP;P=P>P>P?P<P9P7Gop=9A_897p==f5R=A_84;AN8979k8<3>p=8P:P8P6P2P3g00YSR@P=P4P;P<P9P7M<Qp=[P8P9P7P0Cdp=Lg00Z5RA=_87p=ZP8PAP7P0Cdp=VP:P8P6P2P3P@PAP0P9PAP0P7M<Qp=}AN897p=XP:P8P6P2P3P@P;P<P9PAP0P7M<Qp=zAN8979k8<p=x%h8R@%?7R3%:9R6#3RB,57'2%J9RC#0RDg00ZTRE#uRF,;9RG#JRH5>:RI%79RJ/;FRK%7GRL'<P:P8%l:P2%l8%39%37'<A>:9720;9740:XG:X5:PDPK1;7FRKX58RDPCPJP7X58RJ%77X58RCP9P9%@9D^CPPHPLPJPCPGPG%@GD^M<Q%:<RL#O%3L#?1;<FRL,W0%DL%7LRH/<L'2%EL%KH'2'B1;;FRH#7P81W04%D4%74R2/<4'2%E4%K2'2'B%7=P8p-0RM%0ARN#0RO#0RP#0RQ#0,H8%rE,q8RR1H8QRQ5g81H8ORO1H8ARS'6'6RT'6#C1H8NRUAg8RO/6SRR'6,6Q#C16QR#C%CT%c5RT'G'G'G'G%h5R5P81U8<RRP91U8;CbRQ%n8RV%m8RW1IW=1T8ERX&0<E,T8RY'S,1W5AWRZ1i80R[,RY,1W1SX[,1WR\5AW5aW&09>R>PW1i8FR]9`8YR^,F[,1W&08E,T8RE/S^,1W5AW1R^[,1Wf6R^,IWR_5AW5aWP>PW1R[Y,1WR`f7Ra,IW5AWP>A`8X]Rb/SE,1WC9C9C9207W?R?P7P<g00[9Rcg00[YRd'M2067<=>cddB05809H04Rdb7b8b9X28X38X;8X1MX:MW@1<7<,2;Rc%E<%K7Re'2'B%DH1<<H'2%EH/2='B%?4/2a1<H4[[[^28^38^;8^1M^:M^@MP7f8RH#:#3,5a%K;%DaPaP;P9P<P4P^O9b6bHbCbAb>b<C\PIP:%J<RI#0RfP@P7P4%J;Rg/=41e;4%c8RhE8X=:%:;Ri,4IRj%7<Rk%3iRl'5PIPkPJPCP<P<%@<D^PiPl%@lE[%OiRi%?lRl1W0;%D;%7;RC/<;'2%E;%KC'2'BP2P81H8PRP16USRU,6O'6#C16PU#C/GT'GP5PQPVPWAAW_\9aWZP>PW1FYE,1W9AW`P>1FXE,1WR`C9C9P?Pdb7b8b9X28X38X;8X1MX:M124e,Bc%?;15;<'215<;[[^28^38^;8^1M^:MP7%E^%D^P^%:a#3P9P<P=O7b6bAb>b<C\PjPgP:%:7Rg,49P@%0<RjP91=<91L<9PhE8]0^4@R^X=:14AgRcP1P8P@PNP9%Z9%V9PhE8^0cP9%:hRc,4A14AA1500Re1M80RY/}YP7CYPePTP5%{8RZPVPW1F[[,1WP>1IW<C9P?Pdb7b8b9X1MP9\e^1MP7AN80h9>@hReP9O2b6b?P@PNPh%Zh%VhPhE8eW01X97#:R_,4A1X<h,M@P@PN1X<9RN%ZN%VNPhE8eW0X4@X58P9P7O2n10110000020020101100P7O1W0X4@14jgP1P8%04R1/4gP@%0=Rg#0P91=g91Lg9PhE8]0P9%0;/4c141A%34RA/;F/50RcP1PDPAO1PDP4PA%@ACPPYCzP7CYPc%O=%3=#?PTP51U89PVPW1R[X,1WP>PW1Fb[,1WP>1IW;C9C9P?Pdb7b8b9X28X1M15G0P;[\3^28^1MP7Pe%3aP9P<O4b6b<b?P@%01Ph1=1h1L1hPhE8eW0%0a/4_P@P@1y8<R_P_%0HR1/=91=H91LH9;xhP@\@/M_PaP914H6%3HRa/5BPHPa%@aR_P6PB%@BReE[%06RM,411;aF1;BF'5RFP1PDPaO1PDPHPaP_CPPMPDPBO1PDP6PBPeCPE[P7CYPFf9RF#O%3F#?PiPlPTP5P8PRP9PZCbPVPWA`8E],Fb,1WP>P`C9P?Pdb7b8b9X28X3815KG159<[^28^38P7%:=#3f<#3P;O3b6bEb<b?C\O2GwP@%01PN1=1N1L1NPhE8eW0X4@X58P9P7O2n10110000020121101100P7O1W0X4@XD^X=:P7Cvb=P4P7O2b0P@PfP;1=I;1e<;PhE8e%JLP7Etb>WBXF8W4o"). Qed.

Lemma rescale_byte : forall w scale, 0 <= w < 256 -> 0 <= scale < 2^63 ->
  Z.land ((Z.b2z (w <? 1) + -1) mod 18446744073709551616) scale + w = if w =? 0 then w else w + scale.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_x1t_rsc ()) [] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with52Hwh61Hh72Hah84__p1h94__x2h:1bi001bh;1wh<1xh=1yh>2Hsh?1Nh@6__sat0hA6__sat1hB1ei011ehC1ri021rhD5scalehE1zi031np;1p;2p;7p;3p;4p;6p;8g00AUj10Tg005Tj15Tg003^j22Tg004:R0j23Tg00?Hj1<Tg00\9j2LTg00\Vj2XTg00]8j2ITg00]UR1j2PTg00^8j26Tg00^Uj1ATg00:Xj1jTg0062j21Tg00_2j2;Tg00_Rj28Tg00IQj2=Tg00B\j2NTg001Dj7\j6DTg00`0j1[Tg00`Ij2ZTg00`ij2YTg00aQj3WTg00<@j1VTg002^j1UTg00<`j2KTg00=\j1RTg00>:j1QTg00>ej2HTg00?mj2@Tg00MHj4?Tg00b5j6STg00@Pj1TTg00Ldj6mTg00B:j2lTg00C6j2kTg006Oj3>Tg00Cbj3iTg00DAj4hTg00bYj4eTg00c5j1dTg00GUj1cTg00=>j4aTg00A2j3OTg00cSj3bTg00d6j3`Tg00dYj2fTg000Mj6_Tg00N3j7^Tg00NWj7gTg00O_j8]Tg00Q[R2f0R3'=p=7%03#0#0#0p=M%03#0p=Jg00R9R4?>32p=B%03#0#0#0#0#0#0#0p=9f1R5=>43p=:g00[9R6g00e<R77>3p=CP5g00U_R8g00V>R9P9g00V^R:P3g00WeF^p=4P4P5g00XEP3C?p=Gf2R;P8P9P9P:P5P3Fgp=Ff3R<P8P9P9P:P;P5P3G]p=E%75R=g00ZTR>#0R?#0#MR@#JRA#5RB,25'3%5?RC%<>#<#<#<#<#5RD'LRE,25,3=1X<2%B<1I<2'Pf4RF/I2P6P1f5R1#Bf7RG%5>RH'6RI#A%j>RJ'1%0A#J#M#9#9#9#9#9#9RA#0#5RK';f6RL'8/1GP6P4P5PG11GLn0100000020000':P5%BLRMP4P2%73RN123B'3165H#A/1J/;Kf8RO'8/15/:5]5X;41=22122B'31N42W5PGP3P1F\WBP3O1%[MP6PIP7P01653#C1=5;R0[1=3516;5#C[RM16<;#C\01Z53P3n2001000000120000000X=4X<4PM^=4^<4P3POPH1YCD122C%7D122E[[%7CRMg00e\R0AWCD5UW7%7E\0^7Mp-0RMg00U3R0#VRE%U0R01K45RD%R4R1%Q4RPPPP8P9P9P:P41H4>R>g00W>RQ1@42RRC?,4PES%T9RSPP1GR>,4PRTPPP8P9P9P:P<Em5FPPS1@4H/G>,4PCECE1lP:R:P3P;g00[YR<,N61k3;=>6<dAi425ChR2b2b3b4X04W8%B3g00f8[13=;1=H;[[^04^8MP3f;RM/2BPMPFf9RFO4b1b@bAO3b6CeA>67IP6P7%A3/1J/;K/8O/1F11FORI':X:6P4%5@R@#dR6,8GRM113F/:IXE4RIP41LC@RC,;GRBPIP4PGPIPEP0P41K4;P5%c4R;CaP1P41H4?R?9O4>PQAO4?>C?,4PP:P2b2b3b4X04X9411351153':^04^94P3PFPOO2b1PBPEP0PDP1PPP4P>g00XlRD%5ARA,@4C?,4P9FPTPSP4P>PD1@4KC?,4P9FPTCEP:P2b2b3b4X04123A,3N125K,3=[^04P3POPLO2b19bGCEDPMPEP0P;P11@4@,GR,4PP:P2b2b3b4%7@P3b19`G@ED186G1f6GED%A7/1J/;K/8G/1O11OG':e16OHP3E_b6W?P3O1n10210010200021010111103b:bCW>W5XD4X;4o"). Qed.

Lemma x1r_upd_app : forall {X} (pre post : list X) y v, upd (pre ++ y :: post) (length pre) v = pre ++ v :: post.
Proof.
  intros X pre. induction pre as [|a pre IH]; intros post y v; [reflexivity|].
  cbn [app length upd]. rewrite IH. reflexivity.
Qed.

Lemma rw_upd : forall (g : Z -> Z) (ws : list Z) (jk : list byte) k, 0 <= k < zlen ws ->
  upd (map (Z_to_bv 8) (map g (firstn (Z.to_nat k) ws) ++ skipn (Z.to_nat k) ws) ++ jk) (Z.to_nat k) (Z_to_bv 8 (g (Znth k ws)))
  = map (Z_to_bv 8) (map g (firstn (Z.to_nat (k + 1)) ws) ++ skipn (Z.to_nat (k + 1)) ws) ++ jk.
Proof.
  intros g ws jk k K.
  rewrite (firstn_snoc_Znth ws k K).
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  rewrite (skipn_nth_cons ws (Z.to_nat k) 0) by lia.
  rewrite !map_app. cbn [map]. rewrite <- !app_assoc. cbn [app].
  pose proof (x1r_upd_app (map (Z_to_bv 8) (map g (firstn (Z.to_nat k) ws)))
                (map (Z_to_bv 8) (skipn (S (Z.to_nat k)) ws) ++ jk) (Z_to_bv 8 (nth (Z.to_nat k) ws 0))
                (Z_to_bv 8 (g (Znth k ws)))) as U.
  rewrite !length_map, length_firstn, Nat.min_l in U by lia.
  rewrite U. reflexivity.
Qed.

Lemma x1r_nth : forall (g : Z -> Z) (ws : list Z) (jk : list byte) k, 0 <= k < zlen ws ->
  nth_error (map (Z_to_bv 8) (map g (firstn (Z.to_nat k) ws) ++ skipn (Z.to_nat k) ws) ++ jk) (Z.to_nat k)
  = Some (Z_to_bv 8 (Znth k ws)).
Proof.
  intros g ws jk k K.
  rewrite (skipn_nth_cons ws (Z.to_nat k) 0) by lia.
  rewrite map_app, <- app_assoc. cbn [map app].
  rewrite nth_error_app2 by (rewrite !length_map, length_firstn; lia).
  replace (Z.to_nat k - length (map (Z_to_bv 8) (map g (firstn (Z.to_nat k) ws))))%nat with 0%nat
    by (rewrite !length_map, length_firstn; lia).
  reflexivity.
Qed.

Lemma x1r_u8lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z H. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small.
  change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma x1r_rsw1 : forall w scale, 0 <= w < 256 -> 0 <= scale < 2^63 ->
  Z_to_bv 8 (Z.land ((Z.b2z (w <? 1) + -1) mod 18446744073709551616) scale + w) = Z_to_bv 8 (rsw1 scale w).
Proof.
  intros w scale Hw Hs. rewrite rescale_byte by lia. unfold rsw1, to_byte.
  destruct (w =? 0); [reflexivity|]. apply StrFun.Z_to_bv8_mod.
Qed.

Lemma x1r_load : forall l i, 0 <= i < zlen l -> FseNCount.load l i = Ok (Znth i l).
Proof.
  intros l i H. unfold FseNCount.load, FseNCount.Zlength.
  rewrite (proj2 (Z.leb_le 0 i)) by lia. rewrite (proj2 (Z.ltb_lt i (Z.of_nat (length l)))) by lia. reflexivity.
Qed.

Lemma x1r_store : forall l i v, 0 <= i < zlen l -> FseNCount.store l i v = Ok (Zupd i v l).
Proof.
  intros l i v H. unfold FseNCount.store, FseNCount.Zlength.
  rewrite (proj2 (Z.leb_le 0 i)) by lia. rewrite (proj2 (Z.ltb_lt i (Z.of_nat (length l)))) by lia. reflexivity.
Qed.

Lemma x1r_Forall_upd : forall (P : Z -> Prop) n v l, Forall P l -> P v -> Forall P (upd_nat n v l).
Proof.
  intros P n v l. revert n. induction l as [|a l IH]; intros n FA PV.
  - destruct n; cbn [upd_nat]; constructor.
  - inversion FA as [|? ? Pa FL]; subst. destruct n as [|n]; cbn [upd_nat]; constructor; auto.
Qed.

Lemma x1r_sh32 : forall v, 0 <= v < 2^30 -> (Z.shiftl v 32 mod 2^64) / 2^30 = 4 * v.
Proof.
  intros v H. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia.
  replace (v * 2^32) with ((4 * v) * 2^30) by ring. apply Z.div_mul. lia.
Qed.
Lemma x1r_sh32' : forall v, 0 <= v < 2^30 -> Z.shiftr (Z.shiftl v 32 mod 2^64) 30 = 4 * v.
Proof. intros v H. rewrite Z.shiftr_div_pow2 by lia. apply x1r_sh32. exact H. Qed.
Lemma x1r_shl2 : forall v, Z.shiftl v 2 = 4 * v.
Proof. intros v. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

Local Ltac x1r_modsmall := match goal with |- context [?a mod ?b] => rewrite (Z.mod_small a b) by lia end.
Local Ltac rnorm := repeat (first [ rewrite x1r_sh32' by lia | rewrite x1r_shl2 | x1r_modsmall ]); x1w_norm.
Local Ltac walkc := repeat (x1w_zbr; rnorm; x1w_ck); x1w_zbr; rnorm.

Local Ltac xst A ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok usegs _ A _ q (wa (A + q)) ARR ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (A + q) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (A + q) by lia
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?x)) _) =>
    first [ match goal with H : le1 x = [_] |- _ => rewrite H end | rewrite le1_lit ]
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write usegs _ A _ q bb ARR ltac:(rewrite ?upd_length; lia)) as ARR2;
    clear ARR; store_done; rename ARR2 into ARR
  end.

Local Ltac xst4 A ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u32arr_store_ok usegs _ A _ q (wa (A + 4 * q)) ARR ltac:(rewrite ?upd_length, ?length_map; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (A + 4 * q) by lia
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (A + 4 * q) by lia
  end;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le4 ?bb)) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u32arr_write usegs _ A _ q bb ARR ltac:(rewrite ?upd_length, ?length_map; lia)) as ARR2;
    clear ARR; store_done; rename ARR2 into ARR
  end.

Lemma x1r_bind_ok : forall {A B} (a : A) (k : A -> res B), bind (Ok a) k = k a.
Proof. reflexivity. Qed.

Local Ltac dec := first [ let U := fresh "U" in x1w_br U; [exfalso; lia | ]
                        | let U := fresh "U" in x1w_br U; [ | exfalso; lia ] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RW.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x8 x10 x11 x15 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (HW nbS scale : Z) (ws : list Z) (jk : list byte).
  Variable POST : machine_state -> Prop.

  Notation ARRK m1 k := (u8arr usegs m1 HW (map (Z_to_bv 8) (map (rsw1 scale) (firstn (Z.to_nat k) ws) ++ skipn (Z.to_nat k) ws) ++ jk)).

  Lemma rw_loop : 1 <= nbS <= 256 -> zlen ws = nbS -> Forall (fun w => 0 <= w < 256) ws -> 1 <= scale <= 11 ->
    zlen jk = 256 - nbS -> 0 < HW /\ HW + 256 <= 2^47 -> forall f k m1 (x5 x6 x7 x17 : word),
    Z.of_nat f = nbS - k -> 0 <= k < nbS -> x17 = Z_to_bv 64 (18446744073709551615 - HW) -> ARRK m1 k ->
    munch [(HW, HW + 256)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    (forall m2 (y5 y6 y7 : word), ARRK m2 nbS -> munch [(HW, HW + 256)] m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 y6 y7 x8 (Z_to_bv 64 HW) x10 x11 (Z_to_bv 64 scale) (Z_to_bv 64 nbS)
                               (Z_to_bv 64 nbS) x15 (Z_to_bv 64 nbS) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 284)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 (Z_to_bv 64 HW) x10 x11 (Z_to_bv 64 scale) (Z_to_bv 64 nbS)
                            (Z_to_bv 64 nbS) x15 (Z_to_bv 64 k) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 244)) fc None m1 (seg_rom usegs)).
  Proof.
    intros HNS LWS WSR HSC LJK HHW.
    induction f as [|f IH]; intros k m1 x5 x6 x7 x17 FK KR X17 ARR MU WM MI K; [lia|].
    subst x17. unfold PHUF_RDT_X1 in *.
    assert (WR : 0 <= Znth k ws < 256)
      by (unfold Znth; exact (proj1 (Forall_nth (fun w => 0 <= w < 256) ws) WSR (Z.to_nat k) 0 ltac:(lia))).
    assert (LA : length (map (Z_to_bv 8) (map (rsw1 scale) (firstn (Z.to_nat k) ws) ++ skipn (Z.to_nat k) ws) ++ jk) = 256%nat)
      by (repeat first [rewrite length_app | rewrite length_map | rewrite length_firstn | rewrite length_skipn]; lia).
    pose proof (u8arr_read usegs m1 HW _ k _ (wa (HW + k)) ARR (x1r_nth (rsw1 scale) ws jk k ltac:(lia)) ltac:(lia) eq_refl) as RD.
    walkc.
    xst HW ARR k.
    rewrite ?(x1r_u8lit (Znth k ws)) in ARR by lia.
    rewrite (x1r_rsw1 (Znth k ws) scale) in ARR by lia.
    rewrite (rw_upd (rsw1 scale) ws jk k) in ARR by lia.
    x1w_zbr. rnorm. x1w_br BU.
    - eapply IH; [lia | lia | reflexivity | exact ARR | exact MU | exact WM | exact MI | exact K].
    - replace (Z_to_bv 64 (k + 1)) with (Z_to_bv 64 nbS) by (f_equal; lia).
      replace (k + 1) with nbS in ARR by lia.
      eapply K; eassumption.
  Qed.
End RW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SH.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x6 x7 x8 x9 x10 x11 x14 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (WK scale : Z).
  Variable POST : machine_state -> Prop.

  Lemma sh_loop : 1 <= scale <= 11 -> 0 < WK /\ WK + 52 <= 2^47 -> forall f s rank m1 (x5 x13 x15 x17 : word),
    Z.of_nat f = s - scale -> scale < s <= 12 -> zlen rank = 13 -> Forall (fun v => 0 <= v <= 256) rank ->
    x13 = Z_to_bv 64 (18446744073709551615 - WK) -> x15 = Z_to_bv 64 (s - scale) ->
    u32arr usegs m1 WK (map (Z_to_bv 64) rank) ->
    munch [(WK, WK + 52)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    (forall m2 r (y5 y15 y16 y17 : word), shift_rank f s scale rank = Ok r -> u32arr usegs m2 WK (map (Z_to_bv 64) r) ->
       zlen r = 13 -> munch [(WK, WK + 52)] m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
       evt usegs POST (MS (mkR x1 sp gp tp y5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 scale) x13 x14 y15 y16 y17 x18 x19
                               (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 356)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 scale) x13 x14 x15 (Z_to_bv 64 s) x17 x18 x19
                            (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 296)) fc None m1 (seg_rom usegs)).
  Proof.
    intros HSC HWK.
    induction f as [|f IH]; intros s rank m1 x5 x13 x15 x17 FS SR LR RB X13 X15 ARR MU WM MI K; [lia|].
    subst x13 x15. unfold PHUF_RDT_X1 in *.
    assert (RBk : 0 <= Znth (s - scale) rank <= 256)
      by (unfold Znth; exact (proj1 (Forall_nth (fun v => 0 <= v <= 256) rank) RB (Z.to_nat (s - scale)) 0 ltac:(lia))).
    pose proof (u32arr_read usegs m1 WK _ (s - scale) _ (wa (WK + 4 * (s - scale))) ARR
                  (nth_error_map_Znth (Z_to_bv 64) rank (s - scale) ltac:(lia)) ltac:(lia) eq_refl) as RD.
    walkc. x1w_zbr. rnorm.
    xst4 WK ARR s.
    rewrite <- (map_upd_nat (Z_to_bv 64)) in ARR.
    change (upd_nat (Z.to_nat s) (Znth (s - scale) rank) rank) with (Zupd s (Znth (s - scale) rank) rank) in ARR.
    x1w_zbr. rnorm. x1w_br BU.
    - try replace (s + -1) with (s - 1) by lia.
      eapply IH with (s := s - 1) (rank := Zupd s (Znth (s - scale) rank) rank);
        [lia | lia | unfold Zupd; rewrite upd_nat_length; lia | unfold Zupd; apply x1r_Forall_upd; [exact RB | cbv beta; lia]
        | reflexivity | f_equal; lia | exact ARR | exact MU | exact WM | exact MI | ].
      intros m2 r y5 y15 y16 y17 SR2 ARR2 LR2 MU2 WM2 MI2.
      eapply K; try eassumption.
      rewrite shift_rank_S, (x1r_load rank (s - scale)) by lia. rewrite x1r_bind_ok. cbv beta.
      rewrite (x1r_store rank s) by lia. exact SR2.
    - destruct f as [|f]; [|lia].
      eapply K with (r := Zupd s (Znth (s - scale) rank) rank);
        [ rewrite shift_rank_S, (x1r_load rank (s - scale)) by lia; rewrite x1r_bind_ok; cbv beta;
          rewrite (x1r_store rank s) by lia; reflexivity
        | exact ARR | unfold Zupd; rewrite upd_nat_length; lia | exact MU | exact WM | exact MI ].
  Qed.
End SH.

Section ZR.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (x1 x5 x6 x7 x8 x9 x10 x11 x14 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (m : fmem) (WK : Z).
  Variable POST : machine_state -> Prop.

  Lemma zr_loop : 0 < WK /\ WK + 52 <= 2^47 -> forall f s rank m1 (x12 x13 x15 x16 : word),
    Z.of_nat f = s -> 1 <= s <= 12 -> zlen rank = 13 -> x12 = Z_to_bv 64 s ->
    x13 = Z_to_bv 64 (18446744073709551615 - WK) ->
    u32arr usegs m1 WK (map (Z_to_bv 64) rank) ->
    munch [(WK, WK + 52)] m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    (forall m2 r (y15 y16 : word), zero_rank f s rank = Ok r -> u32arr usegs m2 WK (map (Z_to_bv 64) r) -> zlen r = 13 ->
       munch [(WK, WK + 52)] m m2 -> wmono usegs m m2 -> mem_inv usegs m2 ->
       evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 0) x13 x14 y15 y16 x17 x18 x19
                               (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 (PHUF_RDT_X1 + 392)) fc None m2 (seg_rom usegs))) ->
    evt usegs POST (MS (mkR x1 sp gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                            (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 356)) fc None m1 (seg_rom usegs)).
  Proof.
    intros HWK.
    induction f as [|f IH]; intros s rank m1 x12 x13 x15 x16 FS SR LR X12 X13 ARR MU WM MI K; [lia|].
    subst x12 x13. unfold PHUF_RDT_X1 in *.
    walkc.
    xst4 WK ARR s.
    rewrite <- (map_upd_nat (Z_to_bv 64)) in ARR.
    change (upd_nat (Z.to_nat s) 0 rank) with (Zupd s 0 rank) in ARR.
    x1w_zbr. rnorm. x1w_br BU.
    - eapply IH with (s := s - 1) (rank := Zupd s 0 rank);
        [lia | lia | unfold Zupd; rewrite upd_nat_length; lia | f_equal; lia | reflexivity
        | exact ARR | exact MU | exact WM | exact MI | ].
      intros m2 r y15 y16 ZR2 ARR2 LR2 MU2 WM2 MI2.
      eapply K; try eassumption.
      rewrite zero_rank_S, (x1r_store rank s) by lia. exact ZR2.
    - destruct f as [|f]; [|lia].
      replace (Z_to_bv 64 (s + -1)) with (Z_to_bv 64 0) by (f_equal; lia).
      eapply K with (r := Zupd s 0 rank);
        [ rewrite zero_rank_S, (x1r_store rank s) by lia; reflexivity
        | exact ARR | unfold Zupd; rewrite upd_nat_length; lia | exact MU | exact WM | exact MI ].
  Qed.
End ZR.

Section CANSEC. Context {rc : runConstT}.
Section TOP.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT W S mtl lo : Z) (src : list Z).
  Notation SP := (bv_unsigned sp).
  Notation POST := (huf_rdt_post huf_dt_ok ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT W S mtl src lo m).
  Notation WALL := [(bv_unsigned sp - HUF_RDT_STACK, bv_unsigned sp); (DT, DT + DTABLE_BYTES mtl); (W, W + 8704)].

  Hypothesis X396 : forall m1 h ws rank tl jrest jdt jrs jsy j80 j24 (c1 c2 tv x1 x5 x6 x7 x11 x12 x13 x16 x17 x29 x30 x31 : word),
    read_stats src = Ok h -> stats_ok h -> 1 <= hs_ret h <= 129 -> Forall (fun c => 0 <= c < 256) src ->
    1 <= mtl <= 12 -> 0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W mod 8 = 0 -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 -> SP mod 16 = 0 ->
    hk (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 0x01000001))] ->
    u8arr usegs m1 (DT + 4) jdt -> zlen jdt = 4 * 2 ^ mtl ->
    rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) (Z.min (mtl + 1) 11) = Ok (ws, rank, tl) ->
    u8arr usegs m1 (W + 1236) (map (Z_to_bv 8) ws ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
    u32arr usegs m1 W (map (Z_to_bv 64) rank) ->
    u8arr usegs m1 (W + 52) jrs -> zlen jrs = 52 ->
    u8arr usegs m1 (W + 980) jsy -> zlen jsy = 256 ->
    rw_cells usegs m1 (SP + -240) [C8 c1; C8 c2; CB 80 j80; C8 (Z_to_bv 64 W); CB 24 j24] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 tv] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -240) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 (hs_ret h))
                            x11 x12 x13 (Z_to_bv 64 (hs_nbSymbols h)) (Z_to_bv 64 tl) x16 x17 (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 W) s5 s6 s7 s8 s9 s10 s11
                            (Z_to_bv 64 (mtl * 0x01000001)) x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 396)) fc None m1 (seg_rom usegs)).
  Lemma x1_232 : forall m1 h jrest jdt jrs jsy j80 j24 (c1 c2 x1 x5 x6 x7 x16 x17 x29 x30 x31 : word),
    read_stats src = Ok h -> stats_ok h -> 1 <= hs_ret h <= 129 -> Forall (fun c => 0 <= c < 256) src ->
    1 <= mtl <= 12 -> 0 < DT -> DT mod 8 = 0 -> DT + 4 * (1 + 2 ^ mtl) <= lo -> 0 < W -> W mod 8 = 0 -> W + 8704 <= lo ->
    lo <= SP - 4096 -> SP <= 2 ^ 47 -> SP mod 16 = 0 ->
    hk (DT + 4 * (1 + 2 ^ mtl) <= W \/ W + 8704 <= DT) ->
    rw_cells usegs m1 DT [C4 (Z_to_bv 64 (mtl * 0x01000001))] ->
    u8arr usegs m1 (DT + 4) jdt -> zlen jdt = 4 * 2 ^ mtl ->
    hs_tableLog h < Z.min (mtl + 1) 11 ->
    u8arr usegs m1 (W + 1236) (map (Z_to_bv 8) (hs_weights h) ++ jrest) -> zlen jrest = 256 - hs_nbSymbols h ->
    u32arr usegs m1 W (map (Z_to_bv 64) (hs_rank h)) ->
    u8arr usegs m1 (W + 52) jrs -> zlen jrs = 52 ->
    u8arr usegs m1 (W + 980) jsy -> zlen jsy = 256 ->
    rw_cells usegs m1 (SP + -240) [C8 c1; C8 c2; CB 80 j80; C8 (Z_to_bv 64 W); CB 24 j24] ->
    rw_cells usegs m1 (SP + -112) [C4 (Z_to_bv 64 (hs_nbSymbols h))] ->
    rw_cells usegs m1 (SP + -108) [C4 (Z_to_bv 64 (hs_tableLog h))] ->
    rw_cells usegs m1 (SP + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP + -240) ->
    munch WALL m m1 -> wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs POST (MS (mkR x1 (Z_to_bv 64 (SP + -240)) gp tp x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (W + 1236)) (Z_to_bv 64 (hs_ret h))
                            (Z_to_bv 64 (Z.min (mtl + 1) 11)) (Z_to_bv 64 (bv_swrap 32 (Z.min (mtl + 1) 11 - hs_tableLog h)))
                            (Z_to_bv 64 (hs_nbSymbols h)) (Z_to_bv 64 (hs_nbSymbols h)) (Z_to_bv 64 (hs_tableLog h)) x16 x17
                            (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 W) s5 s6 s7 s8 s9 s10 s11
                            (Z_to_bv 64 (mtl * 0x01000001)) x29 x30 x31)
                       F (Z_to_bv 64 (PHUF_RDT_X1 + 232)) fc None m1 (seg_rom usegs)).
  Proof.
    intros m1 h jrest jdt jrs jsy j80 j24 c1 c2 x1 x5 x6 x7 x16 x17 x29 x30 x31 RS SOK RET1 SRCB MTL DT0 DTA DTL W0 WA WL
      LOS SPB SPA DJ RDT RDJ LJD TLT HWr LJR RKr RSa LRS SYa LSY FRa NSr TLr FRb ST MU WM MI.
    pose proof SOK as (TL1 & LWS & NBS & WSR & LRK1 & RKC & KS).
    unfold HufPure_HufStats.HUF_TABLELOG_MAX, HufPure_HufStats.HUF_SYMBOLVALUE_MAX in TL1, NBS, LRK1, RKC.
    unfold FseNCount.Zlength in LWS, LRK1.
    unfold HUF_RDT_STACK, DTABLE_BYTES, HufHarness.DT_BYTES in MU. unfold hk in DJ.
    unfold PHUF_RDT_X1.
    assert (P2 : 2 <= 2^mtl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    pose proof (wf_rank_bounds _ _ _ _ (WF_of_stats h SOK)) as RB.
    assert (WSR8 : Forall (fun w => 0 <= w < 256) (hs_weights h)) by (eapply Forall_impl; [| exact WSR]; cbv beta; intros; lia).
    x1w_zbr. x1w_norm. dec.
    x1w_zto 244. rnorm.
    eapply rw_loop with (HW := W + 1236) (nbS := hs_nbSymbols h) (scale := (Z.min (mtl + 1) 11 - hs_tableLog h)) (ws := hs_weights h) (jk := jrest)
      (f := Z.to_nat (hs_nbSymbols h)) (k := 0) (m := m1) (m1 := m1);
      [ lia | lia | exact WSR8 | lia | lia | lia | lia | lia | first [reflexivity | f_equal; lia] | exact HWr
      | apply munch_refl | apply wmono_refl | exact MI | ].
    intros m2 y5 y6 y7 ARR MU2 WM2 MI2.
    transport_after_call usegs m1 m2 MU2 WM2. clear MU2 WM2 MI.
    rewrite firstn_all2, skipn_all2, app_nil_r in ARR by lia.
    x1w_zbr. x1w_norm. dec.
    x1w_zto 296. rnorm.
    eapply sh_loop with (WK := W) (scale := (Z.min (mtl + 1) 11 - hs_tableLog h)) (s := Z.min (mtl + 1) 11) (rank := hs_rank h)
      (f := Z.to_nat (Z.min (mtl + 1) 11 - (Z.min (mtl + 1) 11 - hs_tableLog h))) (m := m2) (m1 := m2);
      [ lia | lia | lia | lia | lia | exact RB | first [reflexivity | f_equal; lia] | f_equal; lia | exact RKr
      | apply munch_refl | apply wmono_refl | exact MI2 | ].
    intros m3 r1 z5 z15 z16 z17 SR ARR1 LR1 MU3 WM3 MI3.
    transport_after_call usegs m2 m3 MU3 WM3. clear MU3 WM3 MI2.
    eapply zr_loop with (WK := W) (s := (Z.min (mtl + 1) 11 - hs_tableLog h)) (rank := r1) (f := Z.to_nat (Z.min (mtl + 1) 11 - hs_tableLog h)) (m := m3) (m1 := m3);
      [ lia | lia | lia | lia | reflexivity | first [reflexivity | f_equal; lia] | exact ARR1
      | apply munch_refl | apply wmono_refl | exact MI3 | ].
    intros m4 r2 v15 v16 ZR ARR2 LR2 MU4 WM4 MI4.
    transport_after_call usegs m3 m4 MU4 WM4. clear MU4 WM4 MI3.
    x1w_zto 396. rnorm.
    assert (RSCQ : rescale (hs_weights h) (hs_rank h) (hs_nbSymbols h) (hs_tableLog h) (Z.min (mtl + 1) 11)
                  = Ok (map (rsw1 (Z.min (mtl + 1) 11 - hs_tableLog h)) (hs_weights h), r2, Z.min (mtl + 1) 11)).
    { unfold rescale. cbv zeta.
      rewrite (proj2 (Z.ltb_ge (Z.min (mtl + 1) 11) (hs_tableLog h))) by lia.
      rewrite (proj2 (Z.ltb_lt (hs_tableLog h) (Z.min (mtl + 1) 11))) by lia.
      rewrite (proj2 (Z.leb_le _ _)) by first [unfold FseNCount.Zlength; lia | lia].
      cbn [FseNCount.assert bind]. rewrite SR. cbn [bind]. rewrite ZR. cbn [bind].
      rewrite firstn_all2, skipn_all2, app_nil_r by lia. reflexivity. }
    eapply X396 with (h := h) (ws := map (rsw1 (Z.min (mtl + 1) 11 - hs_tableLog h)) (hs_weights h)) (rank := r2) (tl := Z.min (mtl + 1) 11)
      (jrest := jrest) (jdt := jdt) (jrs := jrs) (jsy := jsy) (j80 := j80) (j24 := j24) (c1 := c1) (c2 := c2)
      (tv := Z_to_bv 64 (hs_tableLog h)) (m1 := m4).
    all: first [ exact RSCQ | eassumption | lia | (unfold hk; lia) ].
  Qed.
End TOP.
End CANSEC.
