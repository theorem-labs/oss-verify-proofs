(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: changed GAP, Hp, WINDOW and 33 more; added HRZ, Hlau, Hvl and 16 more; removed tid_chk_0, tid_chk_1; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/Bo0DiagUsageA.v, lines 36, 73-129, 134-221, 244-246. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraMainPhaseA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.
Module NraDiagArms.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraMainPhaseA. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraMainPhaseA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvMain OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmRefuse OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagFwrite OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmMsg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagStrK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmOpen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvLibL OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvLibInit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvOpenFail OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvH OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmRead.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
#[local] Existing Instance PropExec.fx0.

Theorem dg_refuse_ok : forall scfg L C IL, dg_refuse_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & _) Hsp Hal DL _] path fs0 fdata auxvp p1 can A0 _ _.
  exact (refuse_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG M0 fdata path fs0 auxvp p1 can [] A0).
Qed.

Theorem dg_short_ok : forall scfg L C IL, dg_short_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & _ & _ & HDGM) Hsp Hal DL M0def] fs0 fdata auxvp p1 can A0 CAP crC HCAP HLEN Hs.
  exact (short_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDGM M0 M0def fs0 fdata auxvp p1 can [] A0 CAP HCAP crC Hs).
Qed.

Theorem dg_overrun_ok : forall scfg L C IL, dg_overrun_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & _ & _ & HDGM) Hsp Hal DL M0def] fs0 fdata auxvp p1 can A0 CAP crC HCAP HLEN Hge Hov.
  exact (overrun_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDGM M0 M0def fs0 fdata auxvp p1 can [] A0 CAP HCAP crC HLEN Hge Hov).
Qed.

Theorem dg_openerr_ok : forall scfg L C IL, dg_openerr_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & HDGS & _) Hsp Hal DL _] path fs0 fdata p1 cr0 A0 [PLO STR NONUL PLEN PDEF] SAH.
  exact (open_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG HDGS M0 fdata path fs0 p1 [] cr0 A0 (STR_ATA ar sp0 M0 A0 p1 path PLO STR NONUL PLEN PDEF SAH)).
Qed.

Theorem dg_readerr_ok : forall scfg L C IL, dg_readerr_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & HDGS & _) Hsp Hal DL _] fs0 auxvp p1 can cr0 A0 [PLO STR NONUL PLEN PDEF] SAH.
  exact (read_armA scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG HDGS M0 fs0 auxvp p1 can [] cr0 A0 (STR_ATA ar sp0 M0 A0 p1 dot_path PLO STR NONUL PLEN PDEF SAH)).
Qed.

Theorem dg_nofile_ok : forall scfg L C IL Lay LSt, dg_nofile_stmt scfg L C IL Lay LSt.
Proof. intros scfg L C IL Lay LSt. exact (dg_nofile_of_openerr scfg L C IL Lay LSt (dg_openerr_ok scfg L C IL)). Qed.

Theorem dg_dot_ok : forall scfg L C IL Lay LSt, drv_lib_layoutA Lay L -> drv_budgetA L Lay -> dg_dot_stmt scfg L C IL Lay LSt.
Proof. intros scfg L C IL Lay LSt DLL HBUD. exact (dg_dot_of scfg L C IL Lay LSt DLL HBUD (dg_openerr_ok scfg L C IL) (dg_readerr_ok scfg L C IL)). Qed.

(* [comment removed for export] *)
Theorem as0_drv_main_closed : forall scfg (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> lib_statics),
  drv_lib_layoutA Lay L -> drv_lib_cellsA Lay -> drv_budgetA L Lay -> drv_main_stmt scfg L C IL Lay LSt.
Proof.
  intros scfg L C IL Lay LSt DLL DLC HBUD.
  exact (as0_drv_main scfg L C IL Lay LSt DLL DLC HBUD (dg_openerr_ok scfg L C IL) (dg_short_ok scfg L C IL) (dg_overrun_ok scfg L C IL) (dg_refuse_ok scfg L C IL)
           (dg_nofile_ok scfg L C IL Lay LSt) (dg_dot_ok scfg L C IL Lay LSt DLL HBUD)).
Qed.
End NraDiagArms.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed. From Stdlib Require ZArith List Lia Bool. From stdpp.bitvector Require definitions. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DiagUP. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_tL_Mh_0266 () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1N02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes3nat02I46Stdlib9micromega=RingMicromega5Psatz00K46Stdlib9micromega=RingMicromega5Psatz02I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02I46Stdlib9micromega5Tauto8GFormula00K46Stdlib9micromega7EnvRing5PExpr01I46Stdlib9micromega7EnvRing5PExpr00K46Stdlib9micromega7EnvRing5PExpr07I45stdpp9bitvector;definitions2bv00C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK1UC1?~~~~~~~~~~~~~~~I46Stdlib;setoid_ring<Ring_polynom5PExpr00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00I46Stdlib;setoid_ring<Ring_polynom3Pol00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums1Z03C56Stdlib5Arith8PeanoNat3Nat3eqbC45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3powC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr06C56Stdlib6ZArith6BinInt1Z3oppK46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr06C56Stdlib6ZArith6BinInt1Z3mulC45stdpp9bitvector;definitions5bv_eqI47Corelib4Init9Datatypes6option00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init9Datatypes6option02C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic3notC69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7alignedC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega:ZMicromega=Zeval_formulaK47Corelib4Init9Datatypes6option01C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC46Stdlib;setoid_ring;Ring_theory5IDphiC4ELinuxProcessSemantics5Riscv7Prelude5bvmapc69OSSVerify5KrLib7Mh_0266?Na0DiagUsagePre3DUP9usage_midC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specC69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG:diag_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA<zeros_at_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK<u64_of_zerosC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5;defined_subC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP8duA_concC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned?rt_layout_globsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN8cstr_extC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN4cstr00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN<sn_cells_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN8sn_cellsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7div_posC56Stdlib6ZArith6BinInt1ZBdiv_le_upper_boundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK>writable_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG=chk_pre_introC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057:Na0DiagChk7chk_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK8getr_regC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG8cstr_rd1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN5cs_nzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057:Na0DiagChk;strlen_chk1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned9keeps_butC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057:Na0DiagChk7frame72C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK=defined_growsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK8imgc_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK9zeros_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK2URC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC47Corelib4Init5Logic9False_indC69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK=keeps_but_regC1?~~~~~~~~~~~~~~~C35stdpp7tactics<f_equal_helpC69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK4U_toC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_div_plus_fullC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma2C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK7u64_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK7u32_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK6u8_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP8duB_concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk?mem_grows_transC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG>sn_cells_agreeC1?~~~~~~~~~~~~~~~C46Stdlib6ZArith4Zdiv?Z_mod_plus_fullC69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN@wrap_strnlen_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01444L5Kn3L5K4in_bC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG8cstr_nulC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG;u8_of_u32_5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP8duD_concC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC47Corelib4Init5Logic8eq_transC59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib;setoid_ring<Ring_polynom3Pol01K46Stdlib;setoid_ring<Ring_polynom3Pol03C69OSSVerify5KrLib7Mh_00846L5Defs2L55u8_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K45stdpp9bitvector;definitions2bv01K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C46Stdlib9micromega6VarMap4findK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib;setoid_ring<Ring_polynom5PExpr05K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega5Tauto7eval_bfC46Stdlib;setoid_ring<Ring_polynom6PEevalK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega6VarMap1t03I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L5<writable_subC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6or_indC46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib;setoid_ring<Ring_polynom8Pphi_powC69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG5filewC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01K46Stdlib9micromega:ZMicromega;ZArithProof01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C56Stdlib6ZArith6BinInt1Z4of_NC59OSSVerify5KrLib7Mh_0056<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC46Stdlib;setoid_ring;InitialRing9get_signZC69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP6KS_duDC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes3nat01I46Stdlib;setoid_ring<Ring_polynom3Mon00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic4True00C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned2SBC1?~~~~~~~~~~~~~~~I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP6KS_duAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP6KS_duBC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_nil_rC46Stdlib5Lists4List;firstn_all2C47Corelib4Init5Logic8iff_reflC47Corelib4Init5Logic3iffC46Stdlib9micromega;ZifyClasses3injK46Stdlib;setoid_ring<Ring_polynom5PExpr07C47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appC47Corelib5Lists7ListDef6firstnC47Corelib4Init3Nat3subC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG6agree0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duDs_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG>mc_globs_agreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057=Na0AsanMemcpy=mc_icpt_globsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Peano2ltC47Corelib5Lists7ListDef3nthC56Stdlib5Arith8PeanoNat3Nat8sub_diagI47Corelib4Init5Peano2le00C46Stdlib5Lists4List:firstn_appC59OSSVerify5KrLib7Mh_00387SeqExec:rdn_firstnC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0101=Na0DiagMemcpy<zsh_of_hullmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG7stk_zshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG<memcpy_stageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duEa_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK7rdn_imgC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC59OSSVerify5KrLib7Mh_0101=Na0DiagMemcpy3zshC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duFa_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG5rdn_7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK8rdn_xferC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses7rew_iffC46Stdlib9micromega;ZifyClasses5mkrelC69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK9rdn_app_ZC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG>wv_entry_stageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duGa_concC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leC69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duEaC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C46Stdlib9micromega8ZifyInst7Inj_Z_ZC69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4SUF7C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned6LOWENDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4PRE7C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned7HIGHBEGC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned7HIGHENDC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duDsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG8suf7_imgC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG8SUF7_lenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duFaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG7PRE7_eqC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duGaC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duEb_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP:duGb1_concC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z8eqb_reflC69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP:duGb2_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP8KS_duGb1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duEbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP8KS_duGb2C1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duDl_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duEc_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0180:Na0DiagKit2DK8rdn_consC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP9duGc_concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duDlC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duEcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0266=Na0DiagUsageC3DUC8SUF7_eqJC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib4asan9Na0DiagUP9AS0DIAGUP7KS_duGcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250=NraDiagChainK8dg_chainC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3maxc69OSSVerify5KrLib7Mh_0266=Na0DiagUsageB3DUB7usage_BC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0250=NraDiagChainK6dg_wvA00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250=NraDiagChainK7dg_finAC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specK59OSSVerify5KrLib7Mh_0250=NraDiagChainK6dg_wvA01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage7fin_ofUC1?~~~~~~~~~~~~~~~C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage3HSmC1?~~~~~~~~~~~~~~~".
Module Na0DiagUsagePre.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DiagUP. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0RegionPoisoned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0AsanMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180.Na0DiagKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0DiagChk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0DiagMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagStrnlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DiagUP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DUP.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 715744.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1422752.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 91345.       (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.           (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1409024.
  Hypothesis Hp : S <= p /\ p + n + 1 + 9 <= 2 ^ 47.
  Hypothesis Hn : n <= 131071.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.     (* [comment removed for export] *)
  Hypothesis HFMT : L5KA.zeros_at M 2147462296 16.              (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.
  (* [comment removed for export] *)
  Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
  Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
  Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1275136 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
                   /\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.

  (* [comment removed for export] *)
  Definition usage_mid (R' : bvmap 5 word) (M' : word -> option byte) : Prop :=
    (forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M' x = M x) /\ mem_grows M M'
    /\ getr R' (reg 1) = Z_to_bv 64 1315164
    /\ getr R' (reg 10) = Z_to_bv 64 p
    /\ getr R' (reg 11) = Z_to_bv 64 n
    /\ getr R' (reg 12) = Z_to_bv 64 1422752
    /\ getr R' (reg 13) = Z_to_bv 64 (S - 457)
    /\ getr R' (reg 14) = Z_to_bv 64 0
    /\ getr R' (reg 15) = Z_to_bv 64 3
    /\ getr R' (reg 18) = Z_to_bv 64 0
    /\ getr R' (reg 24) = Z_to_bv 64 0
    /\ getr R' (reg 25) = Z_to_bv 64 n
    /\ getr R' (reg 26) = Z_to_bv 64 n
    /\ getr R' (reg 27) = Z_to_bv 64 n
    /\ L5.u64_at RSEGS M' 1422792 (S - 457)
    /\ L5.u64_at RSEGS M' (S - 1016) 0
    /\ L5.u64_at RSEGS M' (S - 992) n
    /\ L5.u64_at RSEGS M' (S - 1008) n
    /\ L5.u64_at RSEGS M' (S - 1024) 69199
    /\ L5.u64_at RSEGS M' (S - 1000) 0
    /\ getr R' (reg 2) = Z_to_bv 64 (S - 1024)
    /\ getr R' (reg 8) = Z_to_bv 64 37
    /\ getr R' (reg 9) = Z_to_bv 64 2147483647
    /\ getr R' (reg 19) = Z_to_bv 64 7
    /\ getr R' (reg 20) = Z_to_bv 64 1422752
    /\ getr R' (reg 21) = Z_to_bv 64 91354
    /\ getr R' (reg 22) = Z_to_bv 64 0
    /\ getr R' (reg 23) = Z_to_bv 64 p
    /\ getr R' (reg 3) = getr R (reg 3)
    /\ getr R' (reg 4) = getr R (reg 4)
    /\ L5.u64_at RSEGS M' (S - 120) 455320
    /\ L5.u64_at RSEGS M' (S - 128) 91345
    /\ L5.u64_at RSEGS M' (S - 136) 1422752
    /\ L5.u64_at RSEGS M' (S - 144) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 152) (U R 19)
    /\ L5.u64_at RSEGS M' (S - 160) (U R 20)
    /\ L5.u64_at RSEGS M' (S - 168) (U R 21)
    /\ L5.u64_at RSEGS M' (S - 176) can
    /\ L5.u64_at RSEGS M' (S - 472) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 184) 0
    /\ L5.u64_at RSEGS M' (S - 216) 0
    /\ L5.u64_at RSEGS M' (S - 208) 0
    /\ L5.u64_at RSEGS M' (S - 200) 0
    /\ L5.u64_at RSEGS M' (S - 192) 0
    /\ L5.u64_at RSEGS M' 1422840 (S - 464)
    /\ L5.u64_at RSEGS M' 1422848 80
    /\ L5.u64_at RSEGS M' 1422808 (S - 464)
    /\ L5.u64_at RSEGS M' 1422760 0
    /\ L5.u64_at RSEGS M' 1422768 0
    /\ L5.u64_at RSEGS M' 1422784 (S - 384)
    /\ L5.u64_at RSEGS M' (S - 488) 1312372
    /\ L5.u64_at RSEGS M' (S - 496) 1422752
    /\ L5.u64_at RSEGS M' (S - 504) 91345
    /\ L5.u64_at RSEGS M' (S - 512) 7027520
    /\ L5.u64_at RSEGS M' (S - 520) 1
    /\ L5.u64_at RSEGS M' (S - 528) 7029528
    /\ L5.u64_at RSEGS M' (S - 536) 5
    /\ L5.u64_at RSEGS M' (S - 544) (U R 22)
    /\ L5.u64_at RSEGS M' (S - 552) (U R 23)
    /\ L5.u64_at RSEGS M' (S - 560) (U R 24)
    /\ L5.u64_at RSEGS M' (S - 568) (U R 25)
    /\ L5.u64_at RSEGS M' (S - 576) (U R 26)
    /\ L5.u64_at RSEGS M' (S - 584) (U R 27)
    /\ L5.u64_at RSEGS M' (S - 960) (S - 216)
    /\ L5.u64_at RSEGS M' (S - 968) (S - 384)
    /\ L5.u64_at RSEGS M' (S - 952) (S - 480)
    /\ L5.u64_at RSEGS M' (S - 936) 0
    /\ L5.u64_at RSEGS M' (S - 928) 7027520
    /\ L5.u64_at RSEGS M' (S - 592) can
    /\ L5.u64_at RSEGS M' (S - 944) 75913
    /\ L5.u64_at RSEGS M' (S - 920) 214748364
    /\ L5.u64_at RSEGS M' (S - 976) 18446744073709486079
    /\ L5.u64_at RSEGS M' (S - 480) (S - 40)
    /\ L5.u64_at RSEGS M' (S - 912) p
    /\ L5.u64_at RSEGS M' (S - 56) 715744
    /\ L5.u64_at RSEGS M' (S - 64) (bv_unsigned (getr R (reg 8)))
    /\ L5.u64_at RSEGS M' (S - 72) (bv_unsigned (getr R (reg 9)))
    /\ L5.u64_at RSEGS M' (S - 80) (bv_unsigned (getr R (reg 18)))
    /\ L5.u64_at RSEGS M' (S - 16) (bv_unsigned (getr R (reg 16)))
    /\ L5.u64_at RSEGS M' (S - 8) (bv_unsigned (getr R (reg 17)))
    /\ L5.u64_at RSEGS M' (S - 48) p
    /\ L5.u64_at RSEGS M' (S - 40) (bv_unsigned (getr R (reg 13)))
    /\ L5.u64_at RSEGS M' (S - 32) (bv_unsigned (getr R (reg 14)))
    /\ L5.u64_at RSEGS M' (S - 24) (bv_unsigned (getr R (reg 15)))
    /\ L5.u64_at RSEGS M' (S - 104) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 88) (S - 48)
    /\ L5.u64_at RSEGS M' (S - 96) (S - 48)
    /\ L5.u64_at RSEGS M' 2147462296 0
    /\ L5.u64_at RSEGS M' 1422824 1308196
    /\ L5.u64_at RSEGS M' 7027520 can
    /\ L5.u64_at RSEGS M' 1412512 1346920
    /\ L5.u64_at RSEGS M' 1412136 1312108
    /\ L5.u64_at RSEGS M' 1440376 2147450880
    /\ L5.u64_at RSEGS M' (S + 8) m8
    /\ L5.u64_at RSEGS M' (S + 16) m7
    /\ L5.u64_at RSEGS M' (S + 24) m6
    /\ L5.u64_at RSEGS M' (S + 32) m5
    /\ L5.u64_at RSEGS M' (S + 40) m4
    /\ L5.u64_at RSEGS M' (S + 48) m3
    /\ L5.u64_at RSEGS M' (S + 56) m2
    /\ L5.u64_at RSEGS M' (S + 64) m1
    /\ L5.u64_at RSEGS M' (S + 72) 1275136
    /\ L5.u32_at RSEGS M' 1422752 5
    /\ L5.u32_at RSEGS M' 1422888 18446744073709551615
    /\ L5.u32_at RSEGS M' 1422872 2
    /\ L5.u32_at RSEGS M' 1422896 4294967295
    /\ L5.u32_at RSEGS M' 1422892 4294967295
    /\ L5.u8_at RSEGS M' 1422752 5
    /\ L5.u8_at RSEGS M' (p + n) 0
    /\ L5.u8_at RSEGS M' (S - 464) 117
    /\ L5.u8_at RSEGS M' (S - 463) 115
    /\ L5.u8_at RSEGS M' (S - 462) 97
    /\ L5.u8_at RSEGS M' (S - 461) 103
    /\ L5.u8_at RSEGS M' (S - 460) 101
    /\ L5.u8_at RSEGS M' (S - 459) 58
    /\ L5.u8_at RSEGS M' (S - 458) 32
    /\ L5.u8_at RSEGS M' 2037244 1
    /\ L5.u8_at RSEGS M' 1443673 1
    /\ L5.u8_at RSEGS M' 1443672 1.

  Theorem usage_pre : exists fx5 R5 M5, msteps RSEGS (st fx R 0x6a2e4 M) (st fx5 R5 0x141280 M5) /\ usage_mid R5 M5.
  Proof.
    destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
    destruct HMF as (MF72 & MF64 & MF56 & MF48 & MF40 & MF32 & MF24 & MF16 & MF8).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    pose proof (u64_of_zeros M 2147462296 (L5KA.zeros_at_sub M 2147462296 16 2147462296 8 HFMT ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as HFMT64.
    assert (Pr : 140735332552704 <= p <= 140737488355318) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    pose proof (duA_conc fx R M (fun j => match j with 2%nat => S | 33%nat => p | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx1 R1 M1 MG1 FR1 FZ1 MS1 KS1.
    assert (AG1 : forall x : word, bv_unsigned x < S - 2352 \/ S <= bv_unsigned x -> M1 x = M x) by (intros x Hx; apply FR1; lia).
    assert (STR1 : cstr M1 p bs t8) by (apply (cstr_ext M M1); [lia | lia | intros x Hx; apply AG1; lia | exact HSTR]).
    assert (HSN1 : sn_cells M1) by (apply (sn_cells_ext M M1); [intros x Hx; apply AG1; lia | exact HSN]).
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (HSH1 : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M1 x = Some (Z_to_bv 8 0)).
    { intros x Hx. rewrite AG1; [apply HSH; exact Hx|]. left. unfold SB in Hx. lia. }
    assert (W1 : L5.writable RSEGS M1 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (CP1 : chk_pre M1 p (n + 1) (S - 2352)).
    { apply chk_pre_intro; try lia. apply (L5.writable_sub RSEGS M1 (S - 5440) 5440); [exact W1 | lia | lia]. destruct HSN1 as (_ & _ & _ & G & _); exact G. exact HSH1. }
    assert (r10 : getr R1 10%bv = Z_to_bv 64 p) by (rewrite <- (getr_reg R1 10 10%bv eq_refl); sc).
    assert (r22 : getr R1 22%bv = Z_to_bv 64 p) by (rewrite <- (getr_reg R1 22 22%bv eq_refl); sc).
    assert (r2 : getr R1 2%bv = Z_to_bv 64 (S - 2352)) by (rewrite <- (getr_reg R1 2 2%bv eq_refl); sc).
    destruct (strlen_chk1 M1 (seg_rom RSEGS) p (S - 2352) bs R1 (cstr_rd1 _ _ _ _ STR1) (cs_nz _ _ _ _ STR1) CP1 r10 r22 r2) as (R2 & M2 & RUN2 & K2 & (AG2 & MG2)).
    assert (AG02 : forall x : word, bv_unsigned x < S - 5440 \/ S <= bv_unsigned x -> M2 x = M x) by (intros x Hx; rewrite AG2 by lia; apply AG1; lia).
    assert (AG12 : forall x : word, bv_unsigned x < S - 2424 \/ S - 2352 <= bv_unsigned x -> M2 x = M1 x) by (intros x Hx; apply AG2; lia).
    assert (W2 : L5.writable RSEGS M2 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D2 : L5.defined M2 (S - 5440) 5440) by (eapply defined_grows; [exact MG2 | eapply defined_grows; eassumption]).
    assert (IMG2 : L5.img_clear M2 65536 1409024) by (apply (imgc_ext M M2); [intros x Hx; apply AG02; lia | lia | lia | exact HIMG]).
    assert (FW2 : L5.writable RSEGS M2 1422752 152) by (eapply writable_grows; [exact MG2 | eapply writable_grows; eassumption]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (SK2 : L5KA.zeros_at M2 (SB + S / 8 - 680) 688).
    { apply (zeros_ext M M2); [intros x Hx; apply AG02; unfold SB in Hx; lia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    pose proof (duB_conc fx1 R2 M2 (fun j => match j with 2%nat => S - 2352 | 33%nat => p | 34%nat => n | 40%nat => can
       | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 120%nat => U R2 20 | 121%nat => U R2 21 | 122%nat => U R2 22 | 123%nat => U R2 23 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx3 R3 M3 MG3 FR3 FZ3 MS3 KS3.
    assert (AG23 : forall x : word, bv_unsigned x < S - 3248 \/ S - 112 <= bv_unsigned x -> ~ filew (bv_unsigned x) -> M3 x = M2 x) by (intros x Hx Hf; unfold filew in Hf; apply FR3; lia).
    assert (A03 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M3 x = M x) by (intros x Hx Hf; rewrite AG23 by (first [exact Hf | lia]); apply AG02; lia).
    assert (MG03 : mem_grows M M3) by (eapply mem_grows_trans; [exact MG1|]; eapply mem_grows_trans; [exact MG2 | exact MG3]).
    assert (W3 : L5.writable RSEGS M3 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D3 : L5.defined M3 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG3 : L5.img_clear M3 65536 1409024) by (apply (imgc_ext M M3); [intros x Hx; apply A03; flia | lia | lia | exact HIMG]).
    assert (STR3 : cstr M3 p bs t8) by (apply (cstr_ext M M3); [lia | lia | intros x Hx; apply A03; flia | exact HSTR]).
    assert (HSN3 : sn_cells M3) by (apply (sn_cells_agree M M3 S); [lia | exact A03 | exact HSN]).
    assert (HSH3 : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M3 x = Some (Z_to_bv 8 0)).
    { intros x Hx. unfold SB in Hx. rewrite A03 by flia. apply HSH. exact Hx. }
    destruct (wrap_strnlen_run fx3 R3 M3 (S - 1024) p bs t8) as (fx4 & R4 & M4 & MS4 & V4 & KS4 & FR4 & MG4);
      [ sc | sc | sc | sc | lia | (replace (S - 1024) with (S + (-64) * 16) by lia); rewrite Z_mod_plus_full; exact Hal
      | dk_gmem | dk_gmem | exact IMG3 | lia | lia | exact STR3 | exact HSH3 | exact HSN3 | ].
    assert (AG34 : forall x : word, bv_unsigned x < S - 5424 \/ S - 1024 <= bv_unsigned x -> M4 x = M3 x) by (intros x Hx; apply FR4; lia).
    assert (A04 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M4 x = M x) by (intros x Hx Hf; rewrite AG34 by lia; apply A03; assumption).
    assert (MG04 : mem_grows M M4) by (eapply mem_grows_trans; eassumption).
    assert (W4 : L5.writable RSEGS M4 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D4 : L5.defined M4 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG4 : L5.img_clear M4 65536 1409024) by (apply (imgc_ext M M4); [intros x Hx; apply A04; flia | lia | lia | exact HIMG]).
    assert (STR4 : cstr M4 p bs t8) by (apply (cstr_ext M M4); [lia | lia | intros x Hx; apply A04; flia | exact HSTR]).
    assert (FW4 : L5.writable RSEGS M4 1422752 152) by (eapply writable_grows; eassumption).
    pose proof (cstr_nul M4 p bs t8 ltac:(lia) ltac:(lia) STR4) as NUL4.
    assert (F84 : L5.u8_at RSEGS M4 1422752 5).
    { apply u8_of_u32_5; [lia | lia|]. scc. }
    pose proof (duD_conc fx4 R4 M4 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | (rkb K2; sc) | shz]).
    dk_open P as fx5 R5 M5 MG5 FR5 FZ5 MS5 KS5.
    assert (AG45 : forall x : word, bv_unsigned x < S - 3248 \/ S - 976 <= bv_unsigned x -> ~ (1422792 <= bv_unsigned x < 1422800) -> M5 x = M4 x) by (intros x Hx Hf; apply FR5; lia).
    assert (AG35 : forall x : word, bv_unsigned x < S - 5424 \/ S - 976 <= bv_unsigned x -> ~ (1422792 <= bv_unsigned x < 1422800) -> M5 x = M3 x) by (intros x Hx Hf; rewrite AG45 by (first [exact Hf | lia]); apply AG34; lia).
    assert (A05 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M5 x = M x) by (intros x Hx Hf; rewrite AG45 by (unfold filew in Hf; lia); apply A04; assumption).
    assert (AG13h : forall x : word, S - 112 <= bv_unsigned x -> M3 x = M1 x) by (intros x Hx; rewrite AG23 by (unfold filew; lia); apply AG12; lia).
    assert (AG15 : forall x : word, S - 112 <= bv_unsigned x -> M5 x = M1 x) by (intros x Hx; rewrite AG35 by lia; apply AG13h; lia).
    clear AG1 AG2 AG02 AG12 AG23 A03 AG34 A04 AG45 AG13h.
    eassert (E2 : getr R5 (reg 2) = Z_to_bv 64 _) by sc. eassert (E8 : getr R5 (reg 8) = Z_to_bv 64 _) by sc. eassert (E9 : getr R5 (reg 9) = Z_to_bv 64 _) by sc.
    eassert (E19 : getr R5 (reg 19) = Z_to_bv 64 _) by sc. eassert (E20 : getr R5 (reg 20) = Z_to_bv 64 _) by sc. eassert (E21 : getr R5 (reg 21) = Z_to_bv 64 _) by sc.
    eassert (E22 : getr R5 (reg 22) = Z_to_bv 64 _) by sc. eassert (E23 : getr R5 (reg 23) = Z_to_bv 64 _) by sc.
    assert (E3 : getr R5 (reg 3) = getr R (reg 3)).
    { rewrite (KS5 3%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (KS4 3%nat) by (cbn; tauto). rewrite (KS3 3%nat) by (apply L5K.in_b; vm_compute; reflexivity).
      transitivity (getr R1 (reg 3)); [rkb K2; reflexivity | apply KS1; apply L5K.in_b; vm_compute; reflexivity]. }
    assert (E4 : getr R5 (reg 4) = getr R (reg 4)).
    { rewrite (KS5 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (KS4 4%nat) by (cbn; tauto). rewrite (KS3 4%nat) by (apply L5K.in_b; vm_compute; reflexivity).
      transitivity (getr R1 (reg 4)); [rkb K2; reflexivity | apply KS1; apply L5K.in_b; vm_compute; reflexivity]. }
    dk_export M5 ltac:(unfold filew; dk_qlia).
    replace (0x6e3d8%bv : word) with (Z_to_bv 64 0x6e3d8) in RUN2 by (apply bv_eq; reflexivity).
    replace (0x6e33c%bv : word) with (Z_to_bv 64 0x6e33c) in RUN2 by (apply bv_eq; reflexivity).
    exists fx5, R5, M5. split.
    { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact MS3|]. eapply msteps_trans; [exact MS4|]. exact MS5. }
    unfold usage_mid. split; [exact A05|]. split; [eapply mem_grows_trans; [exact MG04 | exact MG5]|]. repeat split; assumption.
  Qed.
End UA.
End DUP.

End Na0DiagUsagePre.
Module Na0DiagUsageA.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DiagUP. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0RegionPoisoned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0AsanMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180.Na0DiagKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0DiagChk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0DiagMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagStrnlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DiagUP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266.Na0DiagUsagePre.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DiagUsageA () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2lec69OSSVerify5KrLib7Mh_0266?Na0DiagUsagePre3DUP9usage_preC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0266?Na0DiagUsagePre3DUP9usage_midC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init3Nat3addC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG6agree0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notc69OSSVerify5KrLib7Mh_0266=Na0DiagUsageA3DUA<usage_A_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4PRE7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4SUF7C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DUA.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 715744.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1422752.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 91345.       (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.           (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1409024.
  Hypothesis Hp : S <= p /\ p + n + 1 + 9 <= 2 ^ 47.
  Hypothesis Hn : n <= 66.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.     (* [comment removed for export] *)
  Hypothesis HFMT : L5KA.zeros_at M 2147462296 16.              (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.
  (* [comment removed for export] *)
  Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
  Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
  Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1275136 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
                   /\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.

  Theorem usage_A_tail : forall fx5 R5 M5, DUP.usage_mid R M S p can bs m1 m2 m3 m4 m5 m6 m7 m8 R5 M5 ->
    exists fxE RE ME,
      msteps RSEGS (st fx5 R5 0x141280 M5) (st fxE RE 0x13f6ac ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1422752 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE (reg 22) = Z_to_bv 64 (n + 14)
      /\ L5.u64_at RSEGS ME (S - 584) (S - 464) /\ L5.u64_at RSEGS ME (S - 576) (n + 14) /\ L5.u64_at RSEGS ME (S - 568) 0 /\ L5.u64_at RSEGS ME (S - 560) 0
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) (7 + (length bs + 7)) = Some (PRE7 ++ bs ++ SUF7)
      /\ L5.u32_at RSEGS ME 1422872 2
      /\ agree0 M ME S /\ mem_grows M ME
      (* [comment removed for export] *)
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxF RF MF,
              msteps RSEGS (st fx' RX 0x13f6b8 MX) (st fxF RF 0x137cc8 MF)
              /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
              /\ agree0 M MF S /\ mem_grows M MF
              /\ L5.u32_at RSEGS MF 1422752 5 /\ L5.u64_at RSEGS MF 1422848 0 /\ L5.u64_at RSEGS MF 1422840 7029528
              /\ L5.u64_at RSEGS MF 1422808 0 /\ L5.u64_at RSEGS MF 1422792 0 /\ L5.u64_at RSEGS MF 1422784 0 /\ L5.u64_at RSEGS MF 1422760 0 /\ L5.u64_at RSEGS MF 1422768 0 /\ getr RF (reg 4) = getr R (reg 4)).
  Proof.
    intros fx5 R5 M5 INV.
    destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    assert (Pr : 140735332552704 <= p <= 140737488355318) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    destruct INV as (A05 & MG05 & T). dk_split T.
    assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
    assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
    assert (IMG5 : L5.img_clear M5 65536 1409024) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
    pose proof (duDs_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx6 R6 M6 MG6 FR6 FZ6 MS6 KS6.
    assert (AG56 : forall x : word, bv_unsigned x < S - 1088 \/ S - 1024 <= bv_unsigned x -> M6 x = M5 x) by (intros x Hx; apply FR6; lia).
    assert (A06 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M6 x = M x) by (intros x Hx Hf; rewrite AG56 by lia; apply A05; assumption).
    assert (MG06 : mem_grows M M6) by (eapply mem_grows_trans; eassumption).
    assert (W6 : L5.writable RSEGS M6 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (STR6 : cstr M6 p bs t8) by (apply (cstr_ext M M6); [lia | lia | intros x Hx; apply A06; flia | exact HSTR]).
    assert (HSN6 : sn_cells M6) by (apply (sn_cells_agree M M6 S); [lia | exact A06 | exact HSN]).
    assert (HMC6 : mc_icpt_globs M6) by (apply (mc_globs_agree M M6 S); [lia | exact A06 | exact HMC]).
    assert (SK6 : L5KA.zeros_at M6 (SB + S / 8 - 680) 688).
    { apply (zeros_ext M M6); [intros x Hx; apply A06; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    assert (RDS6 : rdn RSEGS M6 (Z_to_bv 64 p) (length bs) = Some bs).
    { destruct STR6 as [A _ _]. rewrite (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.rdn_firstn RSEGS M6 _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    destruct (memcpy_stage fx6 R6 M6 (S - 1088) (S - 457) p n bs) as (R7 & M7 & MS7 & V7 & KS7 & AG67 & MG7 & RD7);
      [ sc | sc | sc | sc | sc | reflexivity | lia | lia | lia | (right; unfold HIGHBEG, HIGHEND; lia) | (right; unfold HIGHBEG, HIGHEND; lia) | lia | lia | lia | lia | lia
      | dk_gmem | (apply (L5.writable_sub RSEGS M6 (S - 5440) 5440); [exact W6 | lia | lia]) | exact RDS6 | (destruct HSN6 as (_ & _ & _ & G & _); exact G) | exact HMC6
      | (apply (zsh_of_hullm _ p n n); [lia | lia | lia | intros x Hx; assert (0 <= p / 8) by (apply Z.div_pos; lia); rewrite A06 by (unfold SB in Hx; flia); apply HSH; exact Hx])
      | (apply (stk_zsh M6 S); [exact Hal | lia | exact SK6 | lia | lia | lia]) | ].
    assert (A07 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M7 x = M x) by (intros x Hx Hf; rewrite AG67 by lia; apply A06; assumption).
    assert (MG07 : mem_grows M M7) by (eapply mem_grows_trans; eassumption).
    assert (W7 : L5.writable RSEGS M7 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D7 : L5.defined M7 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG7 : L5.img_clear M7 65536 1409024) by (apply (imgc_ext M M7); [intros x Hx; apply A07; flia | lia | lia | exact HIMG]).
    assert (FW7 : L5.writable RSEGS M7 1422752 152) by (eapply writable_grows; eassumption).
    assert (AG67' : forall x : word, S - 1088 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M7 x = M6 x) by (intros x Hx Hd; apply AG67; [lia | exact Hd]).
    assert (AG57 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M7 x = M5 x) by (intros x Hx Hd; rewrite AG67' by (first [exact Hd | lia]); apply AG56; lia).
    assert (AG57s : forall x : word, bv_unsigned x < 2 ^ 32 -> M7 x = M5 x) by (intros x Hx; rewrite AG67 by lia; apply AG56; lia).
    assert (F87 : L5.u8_at RSEGS M7 1422752 5).
    { apply u8_of_u32_5; [lia | lia|]. scc. }
    pose proof (duEa_conc fx6 R7 M7 (fun j => match j with 2%nat => S - 1088 | 33%nat => p | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
    assert (AG78 : forall x : word, bv_unsigned x < S - 1104 \/ S - 1024 <= bv_unsigned x -> ~ (1422792 <= bv_unsigned x < 1422800) -> M8 x = M7 x) by (intros x Hx Hf; apply FR8; lia).
    assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG78 by (unfold filew in Hf; lia); apply A07; assumption).
    assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
    assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (IMG8 : L5.img_clear M8 65536 1409024) by (apply (imgc_ext M M8); [intros x Hx; apply A08; flia | lia | lia | exact HIMG]).
    assert (HSN8 : sn_cells M8) by (apply (sn_cells_agree M M8 S); [lia | exact A08 | exact HSN]).
    assert (HMC8 : mc_icpt_globs M8) by (apply (mc_globs_agree M M8 S); [lia | exact A08 | exact HMC]).
    assert (SK8 : L5KA.zeros_at M8 (SB + S / 8 - 680) 688).
    { apply (zeros_ext M M8); [intros x Hx; apply A08; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    assert (FMT8 : L5KA.zeros_at M8 2147462296 16) by (apply (zeros_ext M M8); [intros x Hx; apply A08; flia | lia | lia | exact HFMT]).
    assert (RDF8 : rdn RSEGS M8 (Z_to_bv 64 91354) (length SUF7) = Some SUF7).
    { rewrite SUF7_len. rewrite (rdn_img M8 65536 1409024) by (first [exact IMG8 | cbn; lia | lia]). exact suf7_img. }
    destruct (memcpy_stage fx8 R8 M8 (S - 1088) (S - 457 + n) 91354 7 SUF7) as (R9 & M9 & MS9 & V9 & KS9 & AG89 & MG9 & RD9);
      [ sc | sc | sc | sc | sc | reflexivity | lia | lia | lia | (left; unfold LOWEND; lia) | (right; unfold HIGHBEG, HIGHEND; lia) | lia | lia | lia | lia | lia
      | dk_gmem | (apply (L5.writable_sub RSEGS M8 (S - 5440) 5440); [exact W8 | lia | lia]) | exact RDF8 | (destruct HSN8 as (_ & _ & _ & G & _); exact G) | exact HMC8
      | | (apply (stk_zsh M8 S); [exact Hal | lia | exact SK8 | lia | lia | lia]) | ].
    { intros x Hx. unfold SB in Hx. change ((2147450880 + 91354 / 8) - (2147450880 + 91354 / 8) mod 8) with 2147462296 in Hx.
      change ((2147450880 + (91354 + 7 - 1) / 8) - (2147450880 + (91354 + 7 - 1) / 8) mod 8 + 8) with 2147462304 in Hx.
      specialize (FMT8 (bv_unsigned x - 2147462296) ltac:(lia)). replace (2147462296 + (bv_unsigned x - 2147462296)) with (bv_unsigned x) in FMT8 by lia.
      rewrite Z_to_bv_bv_unsigned in FMT8. exact FMT8. }
    assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AG89 by lia; apply A08; assumption).
    assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
    assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D9 : L5.defined M9 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG9 : L5.img_clear M9 65536 1409024) by (apply (imgc_ext M M9); [intros x Hx; apply A09; flia | lia | lia | exact HIMG]).
    assert (FW9 : L5.writable RSEGS M9 1422752 152) by (eapply writable_grows; eassumption).
    assert (AG89h : forall x : word, S - 1088 <= bv_unsigned x -> ~ (S - 457 + n <= bv_unsigned x < S - 450 + n) -> M9 x = M8 x) by (intros x Hx Hd; apply AG89; lia).
    assert (AG89s : forall x : word, bv_unsigned x < 2 ^ 32 -> M9 x = M8 x) by (intros x Hx; apply AG89; lia).
    assert (AG79h : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 + n <= bv_unsigned x < S - 450 + n) -> M9 x = M7 x) by (intros x Hx Hd; rewrite AG89h by (first [exact Hd | lia]); apply AG78; lia).
    assert (AG59h : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 450 + n) -> M9 x = M5 x) by (intros x Hx Hd; rewrite AG79h by lia; apply AG57; lia).
    assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422792 <= bv_unsigned x < 1422800) -> M9 x = M5 x).
    { intros x Hx Hf. rewrite AG89s by lia. rewrite AG78 by lia. apply AG57s; lia. }
    pose proof (duFa_conc fx8 R9 M9 (fun j => match j with 2%nat => S - 1088 | 33%nat => p | 34%nat => n | 40%nat => can
       | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 123%nat => U R9 23 | 124%nat => U R9 24 | 125%nat => U R9 25 | 127%nat => U R9 27 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fxE RE ME MGE FRE FZE MSE KSE.
    assert (AG9E : forall x : word, bv_unsigned x < S - 1104 \/ S - 464 <= bv_unsigned x -> ~ (1422792 <= bv_unsigned x < 1422800) -> ME x = M9 x) by (intros x Hx Hf; apply FRE; lia).
    assert (A0E : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> ME x = M x) by (intros x Hx Hf; rewrite AG9E by (unfold filew in Hf; lia); apply A09; assumption).
    assert (MG0E : mem_grows M ME) by (eapply mem_grows_trans; eassumption).
    assert (BUF : rdn RSEGS ME (Z_to_bv 64 (S - 464)) (7 + (length bs + 7)) = Some (PRE7 ++ bs ++ SUF7)).
    { assert (AG5Eb : forall x : word, S - 464 <= bv_unsigned x < S - 457 -> ME x = M5 x) by (intros x Hx; rewrite AG9E by lia; apply AG59h; lia).
      assert (AG7Eb : forall x : word, S - 457 <= bv_unsigned x < S - 457 + n -> ME x = M7 x) by (intros x Hx; rewrite AG9E by lia; apply AG79h; lia).
      assert (AG9Eb : forall x : word, S - 457 + n <= bv_unsigned x < S - 450 + n -> ME x = M9 x) by (intros x Hx; apply AG9E; lia).
      assert (P7 : rdn RSEGS ME (Z_to_bv 64 (S - 464)) 7 = Some PRE7).
      { rewrite PRE7_eq. apply rdn_7; [lia | lia | ..];
          (eapply (u8_ext M5); [intros x Hx; apply AG5Eb; lia | lia | lia |]); match goal with |- L5.u8_at _ _ ?a _ => ring_simplify a end; assumption. }
      assert (PB : rdn RSEGS ME (Z_to_bv 64 (S - 457)) (length bs) = Some bs) by (apply (rdn_xfer M7 ME); [intros x Hx; apply AG7Eb; lia | lia | lia | exact RD7]).
      assert (PS : rdn RSEGS ME (Z_to_bv 64 (S - 457 + n)) 7 = Some SUF7).
      { apply (rdn_xfer M9 ME); [intros x Hx; apply AG9Eb; cbn in Hx; lia | lia | cbn; lia | rewrite SUF7_len in RD9; exact RD9]. }
      apply rdn_app_Z; [lia | lia | exact P7|]. replace (S - 464 + Z.of_nat 7) with (S - 457) by lia.
      apply rdn_app_Z; [lia | lia | exact PB | exact PS]. }
    assert (WE : L5.writable RSEGS ME (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (AG5Es : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422792 <= bv_unsigned x < 1422800) -> ME x = M5 x) by (intros x Hx Hf; rewrite AG9E by lia; apply AG59s; assumption).
    assert (NE : Z.eqb (S - 450 + n) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fxE RE ME 1422752 (S - 592) 0 0 (S - 450 + n) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AGEW & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AGEW by lia; apply A0E; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
    assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) (7 + (length bs + 7)) = Some (PRE7 ++ bs ++ SUF7)).
    { apply (rdn_xfer ME MW); [intros x Hx; apply AGEW; lia | lia | lia | exact BUF]. }
    exists fxE, RW, MW.
    split. { eapply msteps_trans; [exact MS6|]. eapply msteps_trans; [exact MS7|]. eapply msteps_trans; [exact MS8|].
             eapply msteps_trans; [exact MS9|]. eapply msteps_trans; [exact MSE|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 584) with (S - 592 + 8) by lia; exact I0|]. split; [replace (S - 576) with (S - 592 + 16) by lia; replace (n + 14) with (S - 450 + n - (S - 464)) by lia; exact I1|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact I2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact I3|].
    split; [exact BUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = ME x) by (intros x Hx; rewrite AGXW by exact Hx; apply AGEW; lia).
    assert (MGX : mem_grows ME MX) by (eapply mem_grows_trans; eassumption).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX9 : forall x : word, S - 464 <= bv_unsigned x -> ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = M9 x) by (intros x Hx Hd; rewrite AGX by exact Hd; apply AG9E; lia).
    assert (AGX5 : forall x : word, S - 384 <= bv_unsigned x -> MX x = M5 x) by (intros x Hx; rewrite AGX9 by lia; apply AG59h; lia).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGX by lia; apply A0E; assumption).
    assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422792 <= bv_unsigned x < 1422800) -> MX x = M5 x).
    { intros x Hx Hf. rewrite AGX by lia. rewrite AG9E by lia. apply AG59s; assumption. }
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1409024) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1422752 152) by (eapply writable_grows; eassumption).
    pose proof (duGa_conc fx' RX MX (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 41%nat => m1 | 42%nat => m2 | 43%nat => m3 | 44%nat => m4 | 45%nat => m5 | 46%nat => m6 | 47%nat => m7 | 48%nat => m8
       | 118%nat => U RX 18 | 119%nat => U RX 19 | 120%nat => U RX 20 | 122%nat => U RX 22 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc]).
    dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
    exists fxF, RF, MF.
    split; [exact MSF|].
    split. { match goal with H : getr RF (reg 10) = Z_to_bv 64 (U R 8) |- _ => rewrite H end. symmetry. apply U_to. }
    split; [sc|].
    split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. rewrite AGX by lia. apply A0E; [exact Hx | unfold filew; lia]. }
    split; [eapply mem_grows_trans; [exact MG0E|]; eapply mem_grows_trans; [exact MGX | exact MGF]|].
    repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGX5s; lia | lia | lia | eassumption]) | dk_rk].
  Qed.
  Theorem usage_A :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x6a2e4 M) (st fxE RE 0x13f6ac ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1422752 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE (reg 22) = Z_to_bv 64 (n + 14)
      /\ L5.u64_at RSEGS ME (S - 584) (S - 464) /\ L5.u64_at RSEGS ME (S - 576) (n + 14) /\ L5.u64_at RSEGS ME (S - 568) 0 /\ L5.u64_at RSEGS ME (S - 560) 0
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) (7 + (length bs + 7)) = Some (PRE7 ++ bs ++ SUF7)
      /\ L5.u32_at RSEGS ME 1422872 2
      /\ agree0 M ME S /\ mem_grows M ME
      (* [comment removed for export] *)
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxF RF MF,
              msteps RSEGS (st fx' RX 0x13f6b8 MX) (st fxF RF 0x137cc8 MF)
              /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
              /\ agree0 M MF S /\ mem_grows M MF
              /\ L5.u32_at RSEGS MF 1422752 5 /\ L5.u64_at RSEGS MF 1422848 0 /\ L5.u64_at RSEGS MF 1422840 7029528
              /\ L5.u64_at RSEGS MF 1422808 0 /\ L5.u64_at RSEGS MF 1422792 0 /\ L5.u64_at RSEGS MF 1422784 0 /\ L5.u64_at RSEGS MF 1422760 0 /\ L5.u64_at RSEGS MF 1422768 0 /\ getr RF (reg 4) = getr R (reg 4)).
  Proof.
    destruct (DUP.usage_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF) as (fx5 & R5 & M5 & MS5 & INV).
    destruct (usage_A_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
    exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
  Qed.
End UA.
End DUA.

End Na0DiagUsageA.
Module Na0DiagUsageB.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DiagUP. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0RegionPoisoned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0AsanMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180.Na0DiagKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0DiagChk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0DiagMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagStrnlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DiagUP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266.Na0DiagUsagePre.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DiagUsageB () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2InC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00c69OSSVerify5KrLib7Mh_0266?Na0DiagUsagePre3DUP9usage_preC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C45stdpp9bitvector;definitions7Z_to_bvC49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0266?Na0DiagUsagePre3DUP9usage_midC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG6agree0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC47Corelib4Init5Logic3notc69OSSVerify5KrLib7Mh_0266=Na0DiagUsageB3DUB<usage_B_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4PRE7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4SUF7C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DUB.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 715744.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1422752.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 91345.       (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.           (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1409024.
  Hypothesis Hp : S <= p /\ p + n + 1 + 9 <= 2 ^ 47.
  Hypothesis Hn : 67 <= n <= 73.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.     (* [comment removed for export] *)
  Hypothesis HFMT : L5KA.zeros_at M 2147462296 16.              (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.
  (* [comment removed for export] *)
  Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
  Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
  Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1275136 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
                   /\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.

  Theorem usage_B_tail : forall fx5 R5 M5, DUP.usage_mid R M S p can bs m1 m2 m3 m4 m5 m6 m7 m8 R5 M5 ->
    exists fxE RE ME,
      msteps RSEGS (st fx5 R5 0x141280 M5) (st fxE RE 0x13f6ac ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1422752 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 14)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) (n + 7) /\ L5.u64_at RSEGS ME (S - 1112) 91354 /\ L5.u64_at RSEGS ME (S - 1104) 7
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) (7 + length bs) = Some (PRE7 ++ bs) /\ rdn RSEGS ME (Z_to_bv 64 91354) 7 = Some SUF7
      /\ L5.u32_at RSEGS ME 1422872 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x13f6b8 MX) (st fxE2 RE2 0x13f6ac ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 568) /\ getr RE2 (reg 12) = Z_to_bv 64 1
              /\ getr RE2 (reg 9) = Z_to_bv 64 1422752 /\ getr RE2 (reg 18) = Z_to_bv 64 1 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 568) /\ getr RE2 (reg 22) = Z_to_bv 64 0
              /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ L5.u32_at RSEGS ME2 1422872 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x13f6b8 MY) (st fxF RF 0x137cc8 MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1422752 5 /\ L5.u64_at RSEGS MF 1422848 0 /\ L5.u64_at RSEGS MF 1422840 7029528
                      /\ L5.u64_at RSEGS MF 1422808 0 /\ L5.u64_at RSEGS MF 1422792 0 /\ L5.u64_at RSEGS MF 1422784 0 /\ L5.u64_at RSEGS MF 1422760 0 /\ L5.u64_at RSEGS MF 1422768 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    intros fx5 R5 M5 INV.
    destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    assert (Pr : 140735332552704 <= p <= 140737488355318) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    destruct INV as (A05 & MG05 & T). dk_split T.
    assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
    assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
    assert (IMG5 : L5.img_clear M5 65536 1409024) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
    pose proof (duDs_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx6 R6 M6 MG6 FR6 FZ6 MS6 KS6.
    assert (AG56 : forall x : word, bv_unsigned x < S - 1088 \/ S - 1024 <= bv_unsigned x -> M6 x = M5 x) by (intros x Hx; apply FR6; lia).
    assert (A06 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M6 x = M x) by (intros x Hx Hf; rewrite AG56 by lia; apply A05; assumption).
    assert (MG06 : mem_grows M M6) by (eapply mem_grows_trans; eassumption).
    assert (W6 : L5.writable RSEGS M6 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (STR6 : cstr M6 p bs t8) by (apply (cstr_ext M M6); [lia | lia | intros x Hx; apply A06; flia | exact HSTR]).
    assert (HSN6 : sn_cells M6) by (apply (sn_cells_agree M M6 S); [lia | exact A06 | exact HSN]).
    assert (HMC6 : mc_icpt_globs M6) by (apply (mc_globs_agree M M6 S); [lia | exact A06 | exact HMC]).
    assert (SK6 : L5KA.zeros_at M6 (SB + S / 8 - 680) 688).
    { apply (zeros_ext M M6); [intros x Hx; apply A06; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    assert (RDS6 : rdn RSEGS M6 (Z_to_bv 64 p) (length bs) = Some bs).
    { destruct STR6 as [A _ _]. rewrite (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.rdn_firstn RSEGS M6 _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    destruct (memcpy_stage fx6 R6 M6 (S - 1088) (S - 457) p n bs) as (R7 & M7 & MS7 & V7 & KS7 & AG67 & MG7 & RD7);
      [ sc | sc | sc | sc | sc | reflexivity | lia | lia | lia | (right; unfold HIGHBEG, HIGHEND; lia) | (right; unfold HIGHBEG, HIGHEND; lia) | lia | lia | lia | lia | lia
      | dk_gmem | (apply (L5.writable_sub RSEGS M6 (S - 5440) 5440); [exact W6 | lia | lia]) | exact RDS6 | (destruct HSN6 as (_ & _ & _ & G & _); exact G) | exact HMC6
      | (apply (zsh_of_hullm _ p n n); [lia | lia | lia | intros x Hx; assert (0 <= p / 8) by (apply Z.div_pos; lia); rewrite A06 by (unfold SB in Hx; flia); apply HSH; exact Hx])
      | (apply (stk_zsh M6 S); [exact Hal | lia | exact SK6 | lia | lia | lia]) | ].
    assert (A07 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M7 x = M x) by (intros x Hx Hf; rewrite AG67 by lia; apply A06; assumption).
    assert (MG07 : mem_grows M M7) by (eapply mem_grows_trans; eassumption).
    assert (W7 : L5.writable RSEGS M7 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (D7 : L5.defined M7 (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMG7 : L5.img_clear M7 65536 1409024) by (apply (imgc_ext M M7); [intros x Hx; apply A07; flia | lia | lia | exact HIMG]).
    assert (FW7 : L5.writable RSEGS M7 1422752 152) by (eapply writable_grows; eassumption).
    assert (AG67' : forall x : word, S - 1088 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M7 x = M6 x) by (intros x Hx Hd; apply AG67; [lia | exact Hd]).
    assert (AG57 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M7 x = M5 x) by (intros x Hx Hd; rewrite AG67' by (first [exact Hd | lia]); apply AG56; lia).
    assert (AG57s : forall x : word, bv_unsigned x < 2 ^ 32 -> M7 x = M5 x) by (intros x Hx; rewrite AG67 by lia; apply AG56; lia).
    assert (F87 : L5.u8_at RSEGS M7 1422752 5).
    { apply u8_of_u32_5; [lia | lia|]. scc. }
    pose proof (duEb_conc fx6 R7 M7 (fun j => match j with 2%nat => S - 1088 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
    assert (AG78 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> ~ (1422792 <= bv_unsigned x < 1422800) -> M8 x = M7 x) by (intros x Hx Hf; apply FR8; lia).
    assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG78 by (unfold filew in Hf; lia); apply A07; assumption).
    assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
    assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (AG58s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422792 <= bv_unsigned x < 1422800) -> M8 x = M5 x) by (intros x Hx Hf; rewrite AG78 by lia; apply AG57s; lia).
    assert (AG58h : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> M8 x = M5 x) by (intros x Hx Hd; rewrite AG78 by lia; apply AG57; lia).
    assert (NE : Z.eqb (S - 457 + n) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx8 R8 M8 1422752 (S - 1136) 91354 7 (S - 457 + n) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
    assert (IMGW : L5.img_clear MW 65536 1409024) by (apply (imgc_ext M MW); [intros x Hx; apply A0W; flia | lia | lia | exact HIMG]).
    assert (BUFW : rdn RSEGS MW (Z_to_bv 64 (S - 464)) (7 + length bs) = Some (PRE7 ++ bs)).
    { assert (AG5Wb : forall x : word, S - 464 <= bv_unsigned x < S - 457 -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58h; lia).
      assert (AG7Wb : forall x : word, S - 457 <= bv_unsigned x < S - 457 + n -> MW x = M7 x) by (intros x Hx; rewrite AG8W by lia; apply AG78; lia).
      assert (P7 : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 7 = Some PRE7).
      { rewrite PRE7_eq. apply rdn_7; [lia | lia | ..];
          (eapply (u8_ext M5); [intros x Hx; apply AG5Wb; lia | lia | lia |]); match goal with |- L5.u8_at _ _ ?a _ => ring_simplify a end; assumption. }
      assert (PB : rdn RSEGS MW (Z_to_bv 64 (S - 457)) (length bs) = Some bs) by (apply (rdn_xfer M7 MW); [intros x Hx; apply AG7Wb; lia | lia | lia | exact RD7]).
      apply rdn_app_Z; [lia | lia | exact P7|]. replace (S - 464 + Z.of_nat 7) with (S - 457) by lia. exact PB. }
    assert (SUFW : rdn RSEGS MW (Z_to_bv 64 91354) 7 = Some SUF7).
    { rewrite (rdn_img MW 65536 1409024) by (first [exact IMGW | cbn; lia | lia]). exact suf7_img. }
    exists fx8, RW, MW.
    split. { eapply msteps_trans; [exact MS6|]. eapply msteps_trans; [exact MS7|]. eapply msteps_trans; [exact MS8|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 1120) with (S - 1136 + 16) by lia; replace (n + 7) with (S - 457 + n - (S - 464)) by lia; exact I1|].
    split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
    split; [exact BUFW|]. split; [exact SUFW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX7 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M7 x) by (intros x Hx; rewrite AGX8 by lia; apply AG78; lia).
    assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> ~ (S - 457 <= bv_unsigned x < S - 457 + n) -> MX x = M5 x) by (intros x Hx Hd; rewrite AGX7 by lia; apply AG57; lia).
    assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422792 <= bv_unsigned x < 1422800) -> MX x = M5 x) by (intros x Hx Hf; rewrite AGX8 by lia; apply AG58s; assumption).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1409024) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1422752 152) by (eapply writable_grows; eassumption).
    pose proof (duGb1_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
       | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 122%nat => U RX 22 | 123%nat => U RX 23 | 124%nat => U RX 24 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.
    assert (AGX9 : forall x : word, bv_unsigned x < S - 1152 \/ S - 480 <= bv_unsigned x -> ~ (1422784 <= bv_unsigned x < 1422800) -> ~ (1422808 <= bv_unsigned x < 1422816) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
    assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
    assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
    assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422784 <= bv_unsigned x < 1422800) -> ~ (1422808 <= bv_unsigned x < 1422816) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
    assert (EQ : Z.eqb (S - 464) (S - 464) = true) by (apply Z.eqb_refl).
    destruct (wv_entry_stage fx9 R9 M9 1422752 (S - 592) 0 0 (S - 464) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite EQ in X11, X12, X18, X19.
    assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
    assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
    exists fx9, RW2, MW2.
    split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
    split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
    split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
    split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].
    intros fx'' RY MY AGYW MGYW KYW.
    assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
    assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
    assert (AGYX : forall x : word, S - 480 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
    assert (AGY5 : forall x : word, S - 384 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
    assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422784 <= bv_unsigned x < 1422800) -> ~ (1422808 <= bv_unsigned x < 1422816) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
    assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
    assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
    assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGY : L5.img_clear MY 65536 1409024) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
    assert (FWY : L5.writable RSEGS MY 1422752 152) by (eapply writable_grows; eassumption).
    pose proof (duGb2_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 41%nat => m1 | 42%nat => m2 | 43%nat => m3 | 44%nat => m4 | 45%nat => m5 | 46%nat => m6 | 47%nat => m7 | 48%nat => m8
       | 118%nat => U RY 18 | 119%nat => U RY 19 | 120%nat => U RY 20 | 122%nat => U RY 22 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
    exists fxF, RF, MF.
    split; [exact MSF|].
    split. { match goal with H : getr RF (reg 10) = Z_to_bv 64 (U R 8) |- _ => rewrite H end. symmetry. apply U_to. }
    split; [sc|].
    split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGY0; [exact Hx | unfold filew; lia]. }
    split; [eapply mem_grows_trans; [exact MG0Y | exact MGF]|].
    repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGY5s; lia | lia | lia | eassumption]) | dk_rk].
  Qed.

  Theorem usage_B :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x6a2e4 M) (st fxE RE 0x13f6ac ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1422752 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 14)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) (n + 7) /\ L5.u64_at RSEGS ME (S - 1112) 91354 /\ L5.u64_at RSEGS ME (S - 1104) 7
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) (7 + length bs) = Some (PRE7 ++ bs) /\ rdn RSEGS ME (Z_to_bv 64 91354) 7 = Some SUF7
      /\ L5.u32_at RSEGS ME 1422872 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x13f6b8 MX) (st fxE2 RE2 0x13f6ac ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 568) /\ getr RE2 (reg 12) = Z_to_bv 64 1
              /\ getr RE2 (reg 9) = Z_to_bv 64 1422752 /\ getr RE2 (reg 18) = Z_to_bv 64 1 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 568) /\ getr RE2 (reg 22) = Z_to_bv 64 0
              /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ L5.u32_at RSEGS ME2 1422872 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x13f6b8 MY) (st fxF RF 0x137cc8 MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1422752 5 /\ L5.u64_at RSEGS MF 1422848 0 /\ L5.u64_at RSEGS MF 1422840 7029528
                      /\ L5.u64_at RSEGS MF 1422808 0 /\ L5.u64_at RSEGS MF 1422792 0 /\ L5.u64_at RSEGS MF 1422784 0 /\ L5.u64_at RSEGS MF 1422760 0 /\ L5.u64_at RSEGS MF 1422768 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    destruct (DUP.usage_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF) as (fx5 & R5 & M5 & MS5 & INV).
    destruct (usage_B_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
    exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
  Qed.
End UA.
End DUB.

End Na0DiagUsageB.
Module Na0DiagUsageC.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require Na0DiagUP. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5Kn OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144.L5KnA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0RegionPoisoned OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0AsanMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180.Na0DiagKit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057.Na0DiagChk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0101.Na0DiagMemcpy OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagStrnlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagGlue OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.asan.Na0DiagUP OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266.Na0DiagUsagePre.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_Na0DiagUsageC () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01C47Corelib5Lists7ListDef3mapI47Corelib4Init9Datatypes4list00K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG:list_bv_eqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4SUF7C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List2InC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00c69OSSVerify5KrLib7Mh_0266?Na0DiagUsagePre3DUP9usage_preC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib7Mh_0266?Na0DiagUsagePre3DUP9usage_midC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG6agree0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notc69OSSVerify5KrLib7Mh_0266=Na0DiagUsageC3DUC<usage_C_tailC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00306CatSim<msteps_transC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4PRE7C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLia.plia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module DUC.
Import DK. Import DSN. Import DG. Import AS0DIAGUP.

Lemma SUF7_eqJ : SUF7 = map (Z_to_bv 8) [32; 73; 78; 80; 85; 84; 10].
Proof.
ltac2:(KReplay.run1 (kr_t_Na0DiagUsageC ()) [] "p;1p;4p;2p;3p-1R0p10000p4p710R1p9P0p1000Np4p710p8P0p1000ep4p710p8p1001Ep4p70R0p10025p4p710R2p8P0P1p8p1002Qp4p710R0P2p8P0P1p8p1002np4p70R0P2p8P0P1p8p1003\p4p710P1p8p10047p4p710P1p8g004Vj10Tg005;j1>Tg005Yj16Tg006<j15Tg006bj13Tg007@j12Tg007ej1;Tg008Ej44Tg008aj17Tg009Aj28Tg009[j19Tg00:Ej3:Tg00:_j3=Tg00;ej3<Tg00<ER1f1f03<p=1g00<cR0P1g00=c#0R2#0R3#0R4#>R5#6R6%55%04#0#3%23R3#0#0#2#3%23#2#0#3%22#0R2#0#0#0#3%22#0R3#2#3%03#3%32%;1'1'1'1'1'1'1'1R2C4R3%71R4/82P6P1%95R5P0C4P6P1P5P3C45:4d3=o"). Qed.

Section UA.
  Context (fx : FPState).
  Variables (R : bvmap 5 word) (M : word -> option byte) (S p can : Z) (bs t8 : list byte).
  #[local] Notation n := (Z.of_nat (length bs)).
  Hypothesis G1 : getr R (reg 1) = Z_to_bv 64 715744.        (* [comment removed for export] *)
  Hypothesis G2 : getr R (reg 2) = Z_to_bv 64 S.
  Hypothesis G10 : getr R (reg 10) = Z_to_bv 64 1422752.      (* [comment removed for export] *)
  Hypothesis G11 : getr R (reg 11) = Z_to_bv 64 91345.       (* [comment removed for export] *)
  Hypothesis G12 : getr R (reg 12) = Z_to_bv 64 p.           (* [comment removed for export] *)
  Hypothesis HS : 140735332552704 + 5440 <= S <= 140737488355328.
  Hypothesis Hal : S mod 16 = 0.
  Hypothesis HW : L5.writable RSEGS M (S - 5440) 5440.
  Hypothesis HD : L5.defined M (S - 5440) 5440.
  Hypothesis HIMG : L5.img_clear M 65536 1409024.
  Hypothesis Hp : S <= p /\ p + n + 1 + 9 <= 2 ^ 47.
  Hypothesis Hn : 74 <= n <= 131071.
  Hypothesis HSTR : cstr M p bs t8.
  Hypothesis HSH : forall x : word, SB + p / 8 - 7 <= bv_unsigned x < Z.min (SB + (p + n) / 8 + 8) (SB + 2 ^ 44) -> M x = Some (Z_to_bv 8 0).
  Hypothesis HSTK : L5KA.zeros_at M (SB + S / 8 - 680) 688.     (* [comment removed for export] *)
  Hypothesis HFMT : L5KA.zeros_at M 2147462296 16.              (* [comment removed for export] *)
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis HC : diag_cells M can.
  Hypothesis HSN : sn_cells M.
  Hypothesis HMC : mc_icpt_globs M.
  (* [comment removed for export] *)
  Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
  Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
  Hypothesis HMF : L5.u64_at RSEGS M (S + 72) 1275136 /\ L5.u64_at RSEGS M (S + 64) m1 /\ L5.u64_at RSEGS M (S + 56) m2 /\ L5.u64_at RSEGS M (S + 48) m3 /\ L5.u64_at RSEGS M (S + 40) m4
                   /\ L5.u64_at RSEGS M (S + 32) m5 /\ L5.u64_at RSEGS M (S + 24) m6 /\ L5.u64_at RSEGS M (S + 16) m7 /\ L5.u64_at RSEGS M (S + 8) m8.

  Theorem usage_C_tail : forall fx5 R5 M5, DUP.usage_mid R M S p can bs m1 m2 m3 m4 m5 m6 m7 m8 R5 M5 ->
    exists fxE RE ME,
      msteps RSEGS (st fx5 R5 0x141280 M5) (st fxE RE 0x13f6ac ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1422752 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 7)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 7 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 7 = Some PRE7 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1422872 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x13f6b8 MX) (st fxE2 RE2 0x13f6ac ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1422752 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 7
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 7 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7
              /\ L5.u32_at RSEGS ME2 1422872 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x13f6b8 MY) (st fxF RF 0x137cc8 MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1422752 5 /\ L5.u64_at RSEGS MF 1422848 0 /\ L5.u64_at RSEGS MF 1422840 7029528
                      /\ L5.u64_at RSEGS MF 1422808 0 /\ L5.u64_at RSEGS MF 1422792 0 /\ L5.u64_at RSEGS MF 1422784 0 /\ L5.u64_at RSEGS MF 1422760 0 /\ L5.u64_at RSEGS MF 1422768 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    intros fx5 R5 M5 INV.
    destruct Hm as ((Hm1 & Hm2 & Hm3 & Hm4) & (Hm5 & Hm6 & Hm7 & Hm8)).
    pose proof HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & FW).
    assert (Pr : 140735332552704 <= p <= 140737488355318) by lia.
    assert (Nr : 0 <= n <= 131071) by lia.
    assert (DIV : 0 <= (p + n) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (S8 : 0 <= S / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    destruct INV as (A05 & MG05 & T). dk_split T.
    assert (W5 : L5.writable RSEGS M5 (S - 5440) 5440) by (eapply writable_grows; [exact MG05 | exact HW]).
    assert (D5 : L5.defined M5 (S - 5440) 5440) by (eapply defined_grows; [exact MG05 | exact HD]).
    assert (IMG5 : L5.img_clear M5 65536 1409024) by (apply (imgc_ext M M5); [intros x Hx; apply A05; flia | lia | lia | exact HIMG]).
    pose proof (duDl_conc fx5 R5 M5 (fun j => match j with 2%nat => S - 1024 | 33%nat => p | 34%nat => n | 40%nat => can | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx8 R8 M8 MG8 FR8 FZ8 MS8 KS8.
    assert (AG58 : forall x : word, bv_unsigned x < S - 1136 \/ S - 1024 <= bv_unsigned x -> M8 x = M5 x) by (intros x Hx; apply FR8; lia).
    assert (A08 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M8 x = M x) by (intros x Hx Hf; rewrite AG58 by lia; apply A05; assumption).
    assert (MG08 : mem_grows M M8) by (eapply mem_grows_trans; eassumption).
    assert (W8 : L5.writable RSEGS M8 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (NE : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx8 R8 M8 1422752 (S - 1136) p n (S - 457) (S - 464) 2) as (RW & MW & MSW & W17 & W10 & W11 & W12 & W18 & W19 & W22 & KSW & I0 & I1 & I2 & I3 & AG8W & MGW);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE in W11, W12, W18, W19.
    assert (A0W : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW x = M x) by (intros x Hx Hf; rewrite AG8W by lia; apply A08; assumption).
    assert (MG0W : mem_grows M MW) by (eapply mem_grows_trans; eassumption).
    assert (AG5W : forall x : word, S - 1024 <= bv_unsigned x -> MW x = M5 x) by (intros x Hx; rewrite AG8W by lia; apply AG58; lia).
    assert (P7W : rdn RSEGS MW (Z_to_bv 64 (S - 464)) 7 = Some PRE7).
    { rewrite PRE7_eq. apply rdn_7; [lia | lia | ..];
        (eapply (u8_ext M5); [intros x Hx; apply AG5W; lia | lia | lia |]); match goal with |- L5.u8_at _ _ ?a _ => ring_simplify a end; assumption. }
    assert (STRW : cstr MW p bs t8) by (apply (cstr_ext M MW); [lia | lia | intros x Hx; apply A0W; flia | exact HSTR]).
    assert (RDSW : rdn RSEGS MW (Z_to_bv 64 p) (length bs) = Some bs).
    { destruct STRW as [A _ _]. rewrite (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec.rdn_firstn RSEGS MW _ _ _ (length bs) A) by lia. f_equal. rewrite firstn_app, firstn_all2 by lia. rewrite Nat.sub_diag. cbn [firstn]. apply app_nil_r. }
    exists fx8, RW, MW.
    split. { eapply msteps_trans; [exact MS8|]. exact MSW. }
    split; [exact W17|]. split; [exact W10|]. split; [rewrite W11; f_equal; lia|]. split; [exact W12|].
    split; [rewrite (KSW 9%nat) by (cbn; tauto); sc|]. split; [exact W18|]. split; [rewrite W19; f_equal; lia|]. split; [rewrite W22; f_equal; lia|].
    split; [replace (S - 1128) with (S - 1136 + 8) by lia; exact I0|]. split; [replace (S - 457 - (S - 464)) with 7 in I1 by lia; replace (S - 1120) with (S - 1136 + 16) by lia; exact I1|].
    split; [replace (S - 1112) with (S - 1136 + 24) by lia; exact I2|]. split; [replace (S - 1104) with (S - 1136 + 32) by lia; exact I3|].
    split; [exact P7W|]. split; [exact RDSW|]. split; [scc|]. split; [exact A0W|]. split; [exact MG0W|].
    intros fx' RX MX AGXW MGXW KXW.
    assert (AGX8 : forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = M8 x) by (intros x Hx; rewrite AGXW by exact Hx; apply AG8W; lia).
    assert (KX : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr R8 (reg k)) by (intros k Hk; rewrite (KXW k Hk); apply KSW; cbn in Hk |- *; tauto).
    assert (AGX5 : forall x : word, S - 1024 <= bv_unsigned x -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX5s : forall x : word, bv_unsigned x < 2 ^ 32 -> MX x = M5 x) by (intros x Hx; rewrite AGX8 by lia; apply AG58; lia).
    assert (AGX0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MX x = M x) by (intros x Hx Hf; rewrite AGXW by lia; apply A0W; assumption).
    assert (MG0X : mem_grows M MX) by (eapply mem_grows_trans; eassumption).
    assert (WX : L5.writable RSEGS MX (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DX : L5.defined MX (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGX : L5.img_clear MX 65536 1409024) by (apply (imgc_ext M MX); [intros x Hx; apply AGX0; flia | lia | lia | exact HIMG]).
    assert (FWX : L5.writable RSEGS MX 1422752 152) by (eapply writable_grows; eassumption).
    assert (SKX : L5KA.zeros_at MX (SB + S / 8 - 680) 688).
    { apply (zeros_ext M MX); [intros x Hx; apply AGX0; unfold SB in Hx; flia | unfold SB; lia | unfold SB; lia | exact HSTK]. }
    assert (F8X : L5.u8_at RSEGS MX 1422752 5) by (apply u8_of_u32_5; [lia | lia|]; scc).
    pose proof (duEc_conc fx' RX MX (fun j => match j with 2%nat => S - 1136 | 33%nat => p | 34%nat => n | 40%nat => can
       | 22%nat => U R 22 | 23%nat => U R 23 | 24%nat => U R 24 | 25%nat => U R 25 | 26%nat => U R 26 | 27%nat => U R 27
       | 122%nat => U RX 22 | 123%nat => U RX 23 | 125%nat => U RX 25 | 127%nat => U RX 27 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fx9 R9 M9 MG9 FR9 FZ9 MS9 KS9.
    assert (AGX9 : forall x : word, bv_unsigned x < S - 3248 \/ S - 448 <= bv_unsigned x -> ~ (1422784 <= bv_unsigned x < 1422800) -> ~ (1422808 <= bv_unsigned x < 1422816) -> M9 x = MX x) by (intros x Hx Hf1 Hf2; apply FR9; lia).
    assert (A09 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> M9 x = M x) by (intros x Hx Hf; rewrite AGX9 by (unfold filew in Hf; lia); apply AGX0; assumption).
    assert (MG09 : mem_grows M M9) by (eapply mem_grows_trans; eassumption).
    assert (W9 : L5.writable RSEGS M9 (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (AG59s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422784 <= bv_unsigned x < 1422800) -> ~ (1422808 <= bv_unsigned x < 1422816) -> M9 x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGX9 by lia; apply AGX5s; lia).
    assert (NE2 : Z.eqb (S - 457) (S - 464) = false) by (apply Z.eqb_neq; lia).
    destruct (wv_entry_stage fx9 R9 M9 1422752 (S - 592) 0 0 (S - 457) (S - 464) 2) as (RW2 & MW2 & MSW2 & X17 & X10 & X11 & X12 & X18 & X19 & X22 & KSW2 & J0 & J1 & J2 & J3 & AG9W & MGW2);
      [ sc | sc | sc | sc | lia | lia | lia | lia | lia | lia | lia | lia | lia | lia | scc | scc | scc | dk_gmem | ].
    rewrite NE2 in X11, X12, X18, X19.
    assert (A0W2 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MW2 x = M x) by (intros x Hx Hf; rewrite AG9W by lia; apply A09; assumption).
    assert (MG0W2 : mem_grows M MW2) by (eapply mem_grows_trans; eassumption).
    assert (SUF32 : L5.u32_at RSEGS M9 (S - 464) 1347307808) by (apply (OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.Na0DiagFix.DFX.u32_of_u8s M9 (S - 464) (S - 463) (S - 462) (S - 461) 1347307808 32 73 78 80); first [assumption | lia | (vm_compute; reflexivity)]).
    assert (SUFW : rdn RSEGS MW2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7).
    { rewrite SUF7_eq. apply rdn_43; [lia | lia | ..];
        first [ (eapply (u32_ext M9); [intros x Hx; apply AG9W; lia | lia | lia |]) | (eapply (u8_ext M9); [intros x Hx; apply AG9W; lia | lia | lia |]) ];
        match goal with |- _ _ _ ?a _ => ring_simplify a end; assumption. }
    exists fx9, RW2, MW2.
    split. { eapply msteps_trans; [exact MS9|]. exact MSW2. }
    split; [exact X17|]. split; [exact X10|]. split; [rewrite X11; f_equal; lia|]. split; [exact X12|].
    split; [rewrite (KSW2 9%nat) by (cbn; tauto); sc|]. split; [exact X18|]. split; [rewrite X19; f_equal; lia|]. split; [rewrite X22; f_equal; lia|].
    split; [replace (S - 584) with (S - 592 + 8) by lia; exact J0|]. split; [replace (S - 457 - (S - 464)) with 7 in J1 by lia; replace (S - 576) with (S - 592 + 16) by lia; exact J1|].
    split; [replace (S - 568) with (S - 592 + 24) by lia; exact J2|]. split; [replace (S - 560) with (S - 592 + 32) by lia; exact J3|].
    split; [exact SUFW|]. split; [scc|]. split; [exact A0W2|]. split; [exact MG0W2|].
    intros fx'' RY MY AGYW MGYW KYW.
    assert (AGY9 : forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = M9 x) by (intros x Hx; rewrite AGYW by exact Hx; apply AG9W; lia).
    assert (KY : forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr R9 (reg k)) by (intros k Hk; rewrite (KYW k Hk); apply KSW2; cbn in Hk |- *; tauto).
    assert (AGYX : forall x : word, S - 448 <= bv_unsigned x -> MY x = MX x) by (intros x Hx; rewrite AGY9 by lia; apply AGX9; lia).
    assert (AGY5 : forall x : word, S - 448 <= bv_unsigned x -> MY x = M5 x) by (intros x Hx; rewrite AGYX by lia; apply AGX5; lia).
    assert (AGY5s : forall x : word, bv_unsigned x < 2 ^ 32 -> ~ (1422784 <= bv_unsigned x < 1422800) -> ~ (1422808 <= bv_unsigned x < 1422816) -> MY x = M5 x) by (intros x Hx Hf1 Hf2; rewrite AGY9 by lia; apply AG59s; assumption).
    assert (AGY0 : forall x : word, ~ (S - 5440 <= bv_unsigned x < S) -> ~ filew (bv_unsigned x) -> MY x = M x) by (intros x Hx Hf; rewrite AGYW by lia; apply A0W2; assumption).
    assert (MG0Y : mem_grows M MY) by (eapply mem_grows_trans; eassumption).
    assert (WY : L5.writable RSEGS MY (S - 5440) 5440) by (eapply writable_grows; eassumption).
    assert (DY : L5.defined MY (S - 5440) 5440) by (eapply defined_grows; eassumption).
    assert (IMGY : L5.img_clear MY 65536 1409024) by (apply (imgc_ext M MY); [intros x Hx; apply AGY0; flia | lia | lia | exact HIMG]).
    assert (FWY : L5.writable RSEGS MY 1422752 152) by (eapply writable_grows; eassumption).
    pose proof (duGc_conc fx'' RY MY (fun j => match j with 2%nat => S - 592 | 33%nat => p | 34%nat => n | 40%nat => can
       | 8%nat => U R 8 | 9%nat => U R 9 | 18%nat => U R 18 | 19%nat => U R 19 | 20%nat => U R 20 | 21%nat => U R 21 | 22%nat => U R 22
       | 41%nat => m1 | 42%nat => m2 | 43%nat => m3 | 44%nat => m4 | 45%nat => m5 | 46%nat => m6 | 47%nat => m7 | 48%nat => m8
       | 118%nat => U RY 18 | 119%nat => U RY 19 | 120%nat => U RY 20 | 122%nat => U RY 22 | _ => 0 end)) as P. cbn beta iota in P.
    dk_feed P ltac:(first [apply UR | apply U_to | scc | shz]).
    dk_open P as fxF RF MF MGF FRF FZF MSF KSF.
    exists fxF, RF, MF.
    split; [exact MSF|].
    split. { match goal with H : getr RF (reg 10) = Z_to_bv 64 (U R 8) |- _ => rewrite H end. symmetry. apply U_to. }
    split; [sc|].
    split. { intros x Hx Hf. unfold filew in Hf. rewrite FRF by lia. apply AGY0; [exact Hx | unfold filew; lia]. }
    split; [eapply mem_grows_trans; [exact MG0Y | exact MGF]|].
    repeat split; first [sc | (eapply (DK.u64_ext M5); [intros x Hx; rewrite FRF by lia; apply AGY5s; lia | lia | lia | eassumption]) | dk_rk].
  Qed.

  Theorem usage_C :
    exists fxE RE ME,
      msteps RSEGS (st fx R 0x6a2e4 M) (st fxE RE 0x13f6ac ME)
      (* [comment removed for export] *)
      /\ getr RE (reg 17) = Z_to_bv 64 66 /\ getr RE (reg 10) = Z_to_bv 64 2 /\ getr RE (reg 11) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 12) = Z_to_bv 64 2
      /\ getr RE (reg 9) = Z_to_bv 64 1422752 /\ getr RE (reg 18) = Z_to_bv 64 2 /\ getr RE (reg 19) = Z_to_bv 64 (S - 1128) /\ getr RE (reg 22) = Z_to_bv 64 (n + 7)
      /\ L5.u64_at RSEGS ME (S - 1128) (S - 464) /\ L5.u64_at RSEGS ME (S - 1120) 7 /\ L5.u64_at RSEGS ME (S - 1112) p /\ L5.u64_at RSEGS ME (S - 1104) n
      /\ rdn RSEGS ME (Z_to_bv 64 (S - 464)) 7 = Some PRE7 /\ rdn RSEGS ME (Z_to_bv 64 p) (length bs) = Some bs
      /\ L5.u32_at RSEGS ME 1422872 2
      /\ agree0 M ME S /\ mem_grows M ME
      /\ (forall fx' RX MX,
            (forall x : word, ~ (S - 1128 <= bv_unsigned x < S - 1096) -> MX x = ME x) -> mem_grows ME MX ->
            (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RX (reg k) = getr RE (reg k)) ->
            exists fxE2 RE2 ME2,
              msteps RSEGS (st fx' RX 0x13f6b8 MX) (st fxE2 RE2 0x13f6ac ME2)
              (* [comment removed for export] *)
              /\ getr RE2 (reg 17) = Z_to_bv 64 66 /\ getr RE2 (reg 10) = Z_to_bv 64 2 /\ getr RE2 (reg 11) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 12) = Z_to_bv 64 2
              /\ getr RE2 (reg 9) = Z_to_bv 64 1422752 /\ getr RE2 (reg 18) = Z_to_bv 64 2 /\ getr RE2 (reg 19) = Z_to_bv 64 (S - 584) /\ getr RE2 (reg 22) = Z_to_bv 64 7
              /\ L5.u64_at RSEGS ME2 (S - 584) (S - 464) /\ L5.u64_at RSEGS ME2 (S - 576) 7 /\ L5.u64_at RSEGS ME2 (S - 568) 0 /\ L5.u64_at RSEGS ME2 (S - 560) 0
              /\ rdn RSEGS ME2 (Z_to_bv 64 (S - 464)) 7 = Some SUF7
              /\ L5.u32_at RSEGS ME2 1422872 2
              /\ agree0 M ME2 S /\ mem_grows M ME2
              /\ (forall fx'' RY MY,
                    (forall x : word, ~ (S - 584 <= bv_unsigned x < S - 552) -> MY x = ME2 x) -> mem_grows ME2 MY ->
                    (forall k, In k [2; 3; 4; 8; 9; 21; 23; 24; 25; 26; 27]%nat -> getr RY (reg k) = getr RE2 (reg k)) ->
                    exists fxF RF MF,
                      msteps RSEGS (st fx'' RY 0x13f6b8 MY) (st fxF RF 0x137cc8 MF)
                      /\ getr RF (reg 10) = getr R (reg 8) /\ getr RF (reg 2) = Z_to_bv 64 (S + 80)
                      /\ agree0 M MF S /\ mem_grows M MF
                      /\ L5.u32_at RSEGS MF 1422752 5 /\ L5.u64_at RSEGS MF 1422848 0 /\ L5.u64_at RSEGS MF 1422840 7029528
                      /\ L5.u64_at RSEGS MF 1422808 0 /\ L5.u64_at RSEGS MF 1422792 0 /\ L5.u64_at RSEGS MF 1422784 0 /\ L5.u64_at RSEGS MF 1422760 0 /\ L5.u64_at RSEGS MF 1422768 0 /\ getr RF (reg 4) = getr R (reg 4))).
  Proof.
    destruct (DUP.usage_pre fx R M S p can bs t8 G1 G2 G10 G11 G12 HS Hal HW HD HIMG Hp ltac:(lia) HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF) as (fx5 & R5 & M5 & MS5 & INV).
    destruct (usage_C_tail fx5 R5 M5 INV) as (fxE & RE & ME & MSE & REST).
    exists fxE, RE, ME. split; [eapply msteps_trans; [exact MS5 | exact MSE] | exact REST].
  Qed.
End UA.
End DUC.

End Na0DiagUsageC.
From LinuxProcessSemantics.Riscv Require Prelude Instr Sem. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraDrvExit. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
Module NraDiagArmUsage.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraDrvExit. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StreamSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.DrvNodesLazyK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvPiece OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DiagLoopK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintfK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0248.NraDrvPrintf1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraDrvExit OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvG_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvG OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvE OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagChainK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmRefuse OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagStrK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmOpen.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0180. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0144 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0057 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_NraDiagArmUsage () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List8nil_consC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List6nth_okC46Stdlib5Lists4List:firstn_nilK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C59OSSVerify5KrLib7Mh_00634Spec3s2bC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01C45stdpp9bitvector;definitions;bv_unsignedC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG:list_bv_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib7Mh_00634Spec9msg_usageC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K46Stdlib7Strings6String6string01C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4PRE7C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG4SUF7C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK45stdpp9bitvector;definitions2bv01C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib7Mh_0250=NraDiagChainK8dg_chainC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG6agree0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk9mem_growsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250=NraDiagChainK7dg_finAC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C47Corelib4Init5Logic8eq_transK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib7Mh_00846L5Defs2L56u32_atC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L56u64_atC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00306CatSim6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I49OSSVerify5KrLib8PropExec7FPState00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3subK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00C46Stdlib5Lists4List2InC46Stdlib5Lists4List9app_nil_rc69OSSVerify5KrLib7Mh_0266=Na0DiagUsageA3DUA7usage_AC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic3notI59OSSVerify5KrLib7Mh_0250=NraDiagChainK6dg_wvA00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic7f_equalK46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z6to_natK47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z8max_specK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or01K59OSSVerify5KrLib7Mh_0250=NraDiagChainK6dg_wvA01C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage7fin_ofUC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkappI47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op201C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqc59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage3HSmC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums8positive00K46Stdlib9micromega=RingMicromega3Op205c69OSSVerify5KrLib7Mh_0266=Na0DiagUsageC3DUC7usage_CC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z2idI47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib7Mh_01267Na0DrvA4ENVAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250@NraDiagArmRefuse8dg_kn_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State9fd_lookupK4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry01C56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib5Lists4List6concatC59OSSVerify5KrLib7Mh_0250@NraDiagArmRefuse:dg_init_ofC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:NraDrvExit5exitEC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib:NraDrvExit8stdoutPAC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00634Spec5t_dieC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec1WC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec9exit_codeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250=NraDiagChainK8dg_shapeC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG5filewC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387StoreOk>mem_grows_reflC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250=NraDiagChainK<dg_chain_runC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250=NraDiagChainK;dg_shape_eqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg:srz_conseqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I59OSSVerify5KrLib7Mh_0250>NraDiagArmOpen7str_atA00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250@NraDiagArmRefuse>dg_machine_preC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L58writableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L57definedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00846L5Defs2L59img_clearC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250;Na0DiagGlue2DG:diag_cellsC1?~~~~~~~~~~~~~~~I47Corelib5Lists7ListDef6Forall00K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_0089:IcptIfaceA:icl_poisonC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:IcptIfaceA;aicl_poisonC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegK46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05C59OSSVerify5KrLib7Mh_0119;Na0DrvStdio7img_sh0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_01445L5KnA4L5KA8zeros_atC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib7Mh_0250;NraDiagStrK8str_cstrC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN4cstr00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0250;NraDiagStrK8str_hullC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3minC59OSSVerify5KrLib7Mh_0250;NraDiagStrK;str_staticsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0250>Na0DiagStrnlen3DSN8sn_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057=Na0AsanMemcpy=mc_icpt_globsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitionsCZ_to_bv_bv_unsignedC49OSSVerify5KrLib8PropExec9u64_rangeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7and_indC46Stdlib6ZArith:ZArith_dec;Z_le_gt_decC56Stdlib6ZArith6BinInt1Z2gtI47Corelib4Init6Specif7sumbool00c59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage=msg_usage_eqAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage<usage_chainAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage=die_of_chainUC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9app_assocc59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage<usage_chainBC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266?NraDiagArmUsage<usage_chainCC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC59OSSVerify5KrLib7Mh_0089:HeapIfaceA2SBC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0057ANa0RegionPoisoned2SBC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op206". Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Import SX2. Import SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation u64A := (L5Defs.L5.u64_at ASEGS).
#[local] Notation agree0 := Na0DiagGlue.DG.agree0.
#[local] Notation rom := (seg_rom ASEGS).

Lemma msg_usage_eqA : forall a0s, Na0DiagGlue.DG.PRE7 ++ a0s ++ Na0DiagGlue.DG.SUF7 = msg_usage a0s.
Proof.
  intros a0s. unfold msg_usage.
  match goal with |- _ = ?a ++ a0s ++ ?b =>
    replace Na0DiagGlue.DG.PRE7 with a by (apply Na0DiagGlue.DG.list_bv_eq; vm_compute; reflexivity);
    replace Na0DiagGlue.DG.SUF7 with b by (apply Na0DiagGlue.DG.list_bv_eq; vm_compute; reflexivity) end.
  reflexivity.
Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Arm.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Hypothesis ICok : aicpt_ok L ar IL scfg HI.
  Hypothesis ILY : as0_icpt_layout IL.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis Hal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Hypothesis Hex : incl EX_CELLS (asc_cells C).
  Hypothesis Hdg : incl DG_CELLS (asc_cells C).
  Hypothesis Hdgs : incl DGS_CELLS (asc_cells C).
  Variable M0 : word -> option byte.
  Variable fdata : list byte.
  #[local] Notation dinvA := (dinv ar HI sp0 M0).
  #[local] Notation usp := (bv_unsigned sp0).
  #[local] Notation ENVG := (ENVA fdata).

  (* [comment removed for export] *)
  #[using="Type"] Lemma fin_ofU : forall (MV : word -> option byte) (S : Z) (R : bvmap 5 word) (fx' : PropExec.FPState) RX MX,
    getr R 4%bv = Z_to_bv 64 6896384 -> getr R 8%bv = Z_to_bv 64 2 ->
    (exists fxF RF MF,
        msteps ASEGS (@mkst fx' RX (Z_to_bv 64 0x13f6b8) MX rom) (@mkst fxF RF (Z_to_bv 64 0x137cc8) MF rom)
        /\ getr RF 10%bv = getr R 8%bv /\ getr RF 2%bv = Z_to_bv 64 (S + 80)
        /\ agree0 MV MF S /\ mem_grows MV MF
        /\ L5Defs.L5.u32_at ASEGS MF 1422752 5 /\ u64A MF 1422848 0 /\ u64A MF 1422840 7029528
        /\ u64A MF 1422808 0 /\ u64A MF 1422792 0 /\ u64A MF 1422784 0 /\ u64A MF 1422760 0 /\ u64A MF 1422768 0 /\ getr RF 4%bv = getr R 4%bv) ->
    dg_chain usp MV S (S + 80) [] fx' RX 0x13f6b8 MX.
  Proof.
    intros MV S R fx' RX MX G4 G8 (fxF & RF & MF & MSF & F10 & F2 & AGF & MGF & _ & _ & _ & C2 & C1 & _ & C3 & C4 & F4).
    cbn [dg_chain]. exists fxF, RF, MF. split; [exact MSF|]. unfold dg_finA.
    split; [eapply eq_trans; [exact F10 | exact G8]|]. split; [exact F2|]. split; [eapply eq_trans; [exact F4 | exact G4]|]. split; [exact AGF|].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3 | exact C4].
  Qed.

  Section Chains.
    Variables (fxq : PropExec.FPState) (R : bvmap 5 word) (MV : word -> option byte) (S can p : Z) (bs t8 : list byte).
    #[local] Notation n := (Z.of_nat (length bs)).
    #[local] Notation PRE := Na0DiagGlue.DG.PRE7.
    #[local] Notation SUF := Na0DiagGlue.DG.SUF7.
    Hypothesis G1 : getr R 1%bv = Z_to_bv 64 715744.
    Hypothesis G2 : getr R 2%bv = Z_to_bv 64 S.
    Hypothesis G4 : getr R 4%bv = Z_to_bv 64 6896384.
    Hypothesis G10 : getr R 10%bv = Z_to_bv 64 1422752.
    Hypothesis G11 : getr R 11%bv = Z_to_bv 64 91345.
    Hypothesis G8 : getr R 8%bv = Z_to_bv 64 2.
    Hypothesis G12 : getr R 12%bv = Z_to_bv 64 p.
    Hypothesis HS1 : usp - 4096 <= S.
    Hypothesis HS2 : S + 64 <= usp.
    Hypothesis HS16 : S mod 16 = 0.
    Hypothesis HW : L5Defs.L5.writable ASEGS MV (S - 5440) 5440.
    Hypothesis HD : L5Defs.L5.defined MV (S - 5440) 5440.
    Hypothesis HIMG : L5Defs.L5.img_clear MV 65536 1409024.
    Hypothesis Hp : S <= p /\ p + n + 1 + 9 <= 2 ^ 47.
    Hypothesis HSTR : Na0DiagStrnlen.DSN.cstr MV p bs t8.
    Hypothesis HSH : forall x : word, Na0RegionPoisoned.SB + p / 8 - 7 <= bv_unsigned x < Z.min (Na0RegionPoisoned.SB + (p + n) / 8 + 8) (Na0RegionPoisoned.SB + 2 ^ 44) -> MV x = Some (Z_to_bv 8 0).
    Hypothesis HSTK : L5KnA.L5KA.zeros_at MV (Na0RegionPoisoned.SB + S / 8 - 680) 688.
    Hypothesis HFMT : L5KnA.L5KA.zeros_at MV 2147462296 16.
    Hypothesis Hcan : 0 <= can < 2 ^ 64.
    Hypothesis HC : Na0DiagGlue.DG.diag_cells MV can.
    Hypothesis HSN : Na0DiagStrnlen.DSN.sn_cells MV.
    Hypothesis HMC : Na0AsanMemcpy.mc_icpt_globs MV.
    Variables m1 m2 m3 m4 m5 m6 m7 m8 : Z.
    Hypothesis Hm : (0 <= m1 < 2 ^ 64 /\ 0 <= m2 < 2 ^ 64 /\ 0 <= m3 < 2 ^ 64 /\ 0 <= m4 < 2 ^ 64) /\ (0 <= m5 < 2 ^ 64 /\ 0 <= m6 < 2 ^ 64 /\ 0 <= m7 < 2 ^ 64 /\ 0 <= m8 < 2 ^ 64).
    Hypothesis HMF : u64A MV (S + 72) 1275136 /\ u64A MV (S + 64) m1 /\ u64A MV (S + 56) m2 /\ u64A MV (S + 48) m3 /\ u64A MV (S + 40) m4
                     /\ u64A MV (S + 32) m5 /\ u64A MV (S + 24) m6 /\ u64A MV (S + 16) m7 /\ u64A MV (S + 8) m8.

    #[using="sp0 Hsp M0 can p bs HS1 HS2 HS16 Hcan"] Lemma HSm : 140735332552704 + 5440 <= S <= 140737488355328.
Proof.
ltac2:(KReplay.run1 (kr_t_NraDiagArmUsage ()) ["FPX_1"; "Arm"; "Chains"] "h02Hah14__x1h24__x2h31Hh47__arithh54__ffh67__sat10h77__sat11h87__sat12h96__sat9h:8__varmaph;5__with<4cstrp;1p;2p;3p;4p;7p;8p-1R0p10000p4p710R1p9P0p1000Np4p710p8P0g000eR0p4p710p8p1001Ep4p70R2p10025p4p710R3p8P2P1p8p1002Qp4p710R2P3p8P2P1p8p1002np4p70R2P3p8P2P1p8p1003\p4p710P1p8p10047p4p710P1p8g008Qj11Tg004Vj10Tg0096j15Tg005;j1@Tg00:Nj2STg00Tfj22Tg00UBj2CTg00M<j2ATg005Yj1gTP0j2eTg00U_j1^Tg00VDj1ZTg00Vdj2ITg00WLj2?Tg00Whj3HTg00XLj1=Tg00Xkj2:Tg00YTj3>Tg00Z=j2FTg009Tj1VTg00>7j3ETg006<j1UTg00Zij2RTg00[Gj1QTg00[ej4PTg00\Cj1OTg00\aj1NTg00]Lj2DTg00]oj3MTg00^Rj1TTg00_4j3LTg00_Wj3fTg00`:j2dTg00:4j2cTg00`\j2bTg00;Tj3]Tg00aHj3\Tg00agj4[Tg00HZj2JTg00bYj2YTg00c6j2_Tg00cYj4XTg00dDj7`Tg00dhj7aTg00eLj8WTf0R0#1#1p=K%10#1#1#1p=<%00#0p=3%00#0#0#0p=;%00#0#0#0#0#0#0#0p=4g00S5R1/20p=9g00?RR2/_0p=6P2f1R3g00f0P0CXp=7P3g00fWR4g00g6R5P5g00gVR6P0g00h6F`p=8f2R7P4P5P5P6P3P0Fap=Gf3R8P4P5P5P6P7P3P0GWp=Bp,3Hspg00@0R4#K#<#<#<R9#1#0#3#;#4#4#4#5R:%04R;#3R<#0#3R=#@p,3sp0'SR>'2%5;R?%1;R@#1#KRA#5RB'CRC,2>'A%@<#gp,2bs'eR<#^%Z<#91I?B1?1?R<%9B1?1C[[%9?RDg00hVREAH?B3UW0%9C\E^0D%5=RB,I?%9B1C?BRF,?1[\<AH?B3VEX0D%9F\E^0Dg00i2RDg00i^RE#=RF#=R<#=RG,:21:2<1:2ERE5>25>2g00j=R<'F%=G,:21:2F=>2E5>2/F<%VD5ED3E%UDP21R27P3%Q2CP%O2%N2RD%6:1D2;R;'7,8D%6?%@A5M2,7;,8D5GD%T5R5PD1D24R4%6B5L2/7;,8DP5PD%3=#;R=#5RA#69f2;/74,8DP5%09#<#<#3#;#1#0#3#1#;#4#5R9#6%0@#1#0#1#3#;#5R@#65L2/74,8D%0=#3#4#4#4#4#5R=#6,74,8D5GDCBCBCB1dD6P0P7g00jiRDg00@UR6'c1b07=]D6dA\213C[b5b:b;X12X2212:3123C'A1J3B/271Y8A/271J9@/28128='A[[[^12^22P0P>p,1Sf6p,3HS2p,3HS1O5b4b9b6b7b8b<b3o"). Qed.

    #[using="Hsp M0 can p t8 G1 G2 G4 G10 G11 G8 G12 HS1 HS2 HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT Hcan HC HSN HMC m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF"] Lemma usage_chainA : n <= 66 -> dg_chain usp MV S (S + 80) [PRE ++ bs ++ SUF] fxq R 0x6a2e4 MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Na0DiagUsageA.DUA.usage_A fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN HMC m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & FDc & AGE & MGE & POST).
      cbn [dg_chain]. exists fxE, RE, ME, (S - 584), (S - 584), 2, (S - 464), (n + 14), 0, 0, (PRE ++ bs ++ SUF), (@nil byte).
      split; [exact MS|].
      split.
      { constructor.
        - exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj (eq_trans E22 (f_equal (Z_to_bv 64) (eq_sym (Z.add_0_r _)))) E19))))))).
        - lia.
        - split; [exact I0|]. replace (S - 584 + 8) with (S - 576) by lia. exact I1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|].
          replace (Z.to_nat (n + 14)) with (7 + (length bs + 7))%nat by lia. exact BUF.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 584 + 16) with (S - 568) by lia; exact I2|]. split; [replace (S - 584 + 24) with (S - 560) by lia; exact I3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
        - lia.
        - exact FDc. }
      split; [rewrite app_nil_r; reflexivity|]. split; [exact AGE|].
      intros RX MX FRX GRX KX.
      exact (fin_ofU MV S R fxE RX MX G4 G8 (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX)).
    Qed.

    #[using="Hsp M0 can p t8 G1 G2 G4 G10 G11 G8 G12 HS1 HS2 HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT Hcan HC HSN HMC m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF"] Lemma usage_chainB : 67 <= n <= 73 -> dg_chain usp MV S (S + 80) [(PRE ++ bs) ++ SUF; []] fxq R 0x6a2e4 MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Na0DiagUsageB.DUB.usage_B fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN HMC m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & BUF2 & FDc & AGE & MGE & POST).
      cbn [dg_chain]. exists fxE, RE, ME, (S - 1128), (S - 1128), 2, (S - 464), (n + 7), 91354, 7, (PRE ++ bs), SUF.
      split; [exact MS|].
      split.
      { constructor.
        - replace (n + 14) with (n + 7 + 7) in E22 by lia. exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj E22 E19))))))).
        - lia.
        - split; [exact I0|]. replace (S - 1128 + 8) with (S - 1120) by lia. exact I1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|].
          replace (Z.to_nat (n + 7)) with (7 + length bs)%nat by lia. exact BUF.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 1128 + 16) with (S - 1112) by lia; exact I2|]. split; [replace (S - 1128 + 24) with (S - 1104) by lia; exact I3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; left; lia|]. split; [right; left; lia|]. exact BUF2.
        - lia.
        - exact FDc. }
      split; [reflexivity|]. split; [exact AGE|].
      intros RX MX FRX GRX KX.
      destruct (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX)
        as (fxE2 & RE2 & ME2 & MS2 & Q17 & Q10 & Q11 & Q12 & Q9 & Q18 & Q19 & Q22 & J0 & J1 & FDc2 & AGE2 & MGE2 & POST2).
      cbn [dg_chain]. exists fxE2, RE2, ME2, (S - 584), (S - 568), 1, 0, 0, 0, 0, (@nil byte), (@nil byte).
      split; [exact MS2|].
      split.
      { constructor.
        - exact (conj Q17 (conj Q10 (conj Q11 (conj Q12 (conj Q9 (conj Q18 (conj Q22 Q19))))))).
        - lia.
        - split; [exact J0|]. replace (S - 568 + 8) with (S - 560) by lia. exact J1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
        - intros _. split; reflexivity.
        - intros X. discriminate X.
        - lia.
        - exact FDc2. }
      split; [reflexivity|]. split; [exact AGE2|].
      intros RY MY FRY GRY KY.
      exact (fin_ofU MV S R fxE2 RY MY G4 G8 (POST2 fxE2 RY MY (fun x Hx => FRY x (fun X => Hx ltac:(lia))) GRY KY)).
    Qed.

    #[using="Hsp M0 can p t8 G1 G2 G4 G10 G11 G8 G12 HS1 HS2 HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF"] Lemma usage_chainC : 74 <= n <= 131071 -> dg_chain usp MV S (S + 80) [PRE ++ bs; SUF] fxq R 0x6a2e4 MV.
    Proof.
      intros Hn. pose proof Hsp as Hsp'.
      destruct (Na0DiagUsageC.DUC.usage_C fxq R MV S p can bs t8 G1 G2 G10 G11 G12 HSm HS16 HW HD HIMG Hp Hn HSTR HSH HSTK HFMT Hcan HC HSN m1 m2 m3 m4 m5 m6 m7 m8 Hm HMF)
        as (fxE & RE & ME & MS & E17 & E10 & E11 & E12 & E9 & E18 & E19 & E22 & I0 & I1 & I2 & I3 & BUF & BUF2 & FDc & AGE & MGE & POST).
      cbn [dg_chain]. exists fxE, RE, ME, (S - 1128), (S - 1128), 2, (S - 464), 7, p, n, PRE, bs.
      split; [exact MS|].
      split.
      { constructor.
        - replace (n + 7) with (7 + n) in E22 by lia. exact (conj E17 (conj E10 (conj E11 (conj E12 (conj E9 (conj E18 (conj E22 E19))))))).
        - lia.
        - split; [exact I0|]. replace (S - 1128 + 8) with (S - 1120) by lia. exact I1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|]. exact BUF.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 1128 + 16) with (S - 1112) by lia; exact I2|]. split; [replace (S - 1128 + 24) with (S - 1104) by lia; exact I3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|].
          rewrite Nat2Z.id. exact BUF2.
        - lia.
        - exact FDc. }
      split; [reflexivity|]. split; [exact AGE|].
      intros RX MX FRX GRX KX.
      destruct (POST fxE RX MX (fun x Hx => FRX x (fun X => Hx ltac:(lia))) GRX KX)
        as (fxE2 & RE2 & ME2 & MS2 & Q17 & Q10 & Q11 & Q12 & Q9 & Q18 & Q19 & Q22 & J0 & J1 & J2 & J3 & BUF3 & FDc2 & AGE2 & MGE2 & POST2).
      cbn [dg_chain]. exists fxE2, RE2, ME2, (S - 584), (S - 584), 2, (S - 464), 7, 0, 0, SUF, (@nil byte).
      split; [exact MS2|].
      split.
      { constructor.
        - exact (conj Q17 (conj Q10 (conj Q11 (conj Q12 (conj Q9 (conj Q18 (conj Q22 Q19))))))).
        - lia.
        - split; [exact J0|]. replace (S - 584 + 8) with (S - 576) by lia. exact J1.
        - split; [lia|]. split; [lia|]. split; [lia|]. split; [right; right; lia|]. split; [right; right; lia|]. exact BUF3.
        - intros X. discriminate X.
        - intros _. split; [replace (S - 584 + 16) with (S - 568) by lia; exact J2|]. split; [replace (S - 584 + 24) with (S - 560) by lia; exact J3|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [left; reflexivity|]. split; [left; reflexivity|]. reflexivity.
        - lia.
        - exact FDc2. }
      split; [rewrite app_nil_r; reflexivity|]. split; [exact AGE2|].
      intros RY MY FRY GRY KY.
      exact (fin_ofU MV S R fxE2 RY MY G4 G8 (POST2 fxE2 RY MY (fun x Hx => FRY x (fun X => Hx ltac:(lia))) GRY KY)).
    Qed.
  End Chains.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex"] Lemma die_of_chainU : forall parts msg vals kn LB LK cr A M (model : Model) (fxq : PropExec.FPState) R fs (S : Z),
    know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) kn -> dg_kn_ok kn = true -> vals_ev vals 0 = sp0 ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    usp - 4096 <= S -> S + 80 <= usp -> S mod 16 = 0 ->
    concat parts = msg ->
    dg_chain usp (mrestrict (ahid A model) M) S (S + 80) parts fxq R 0x6a2e4 (mrestrict (ahid A model) M) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x6a2e4) M rom) model) (t_die msg fs).
  Proof.
    intros parts msg vals kn LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2 HS1 HS2 HS16 Ecat CH.
    destruct (dg_init_of sp0 Hsp M0 fdata vals kn _ HK OKb P0) as (WINi & IMGi & XAi & SOPi).
    unfold t_die. rewrite <- Ecat.
    eapply srz_conseq; [|apply dg_shape_eq].
    assert (HSf16 : (S + 80) mod 16 = 0).
    { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - HS16. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    exact (dg_chain_run scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL Hex M0 parts LB LK cr A _ S (S + 80) (bv_unsigned (vals_ev vals 4)) fs fxq R 0x6a2e4 M model D EFS
             (fun x _ _ => eq_refl) (mem_grows_refl _) ltac:(lia) ltac:(lia) HSf16 WINi IMGi XAi SOPi FD2 CH).
  Qed.

  (* [comment removed for export] *)
  #[using="L C IL HIok ICok ILY Hsp Hal DL Hex Hdg Hdgs"] Lemma dg_usage_site : forall (fxq : PropExec.FPState) vals kn R M (model : Model) LB LK cr A fs (p0 : word) (a0s : list byte) (fr : Z -> word),
    know_ok ASEGS (ENVG vals) (mrestrict (ahid A model) M) kn -> dg_kn_ok kn = true -> vals_ev vals 0 = sp0 ->
    getr R 1%bv = Z_to_bv 64 715744 -> getr R 2%bv = Z_to_bv 64 (usp - 128) -> getr R 4%bv = Z_to_bv 64 6896384 -> getr R 8%bv = Z_to_bv 64 2 ->
    getr R 10%bv = Z_to_bv 64 1422752 -> getr R 11%bv = Z_to_bv 64 91345 -> getr R 12%bv = p0 ->
    dinvA LB LK cr A M model -> m_fs model = fs -> fd_lookup (m_fds model) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    str_atA ar sp0 M0 A p0 a0s ->
    rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1275136)) ->
    (forall k, In k [64; 72; 80; 88; 96; 104; 112; 120] -> rdn ASEGS (mrestrict (ahid A model) M) (Z_to_bv 64 (usp - k)) 8 = Some (word_to_le_bytes 8 (fr k))) ->
    srealizes ASEGS scfg (mkCfg (@mkst fxq R (Z_to_bv 64 0x6a2e4) M rom) model) (t_die (msg_usage a0s) fs).
  Proof.
    intros fxq vals kn R M model LB LK cr A fs p0 a0s fr HK OKb P0 G1 G2 G4 G8 G10 G11 G12p D EFS FD2 [PLO STR NONUL PLEN PDEF SAH] FRA FRK. pose proof Hsp as Hsp'.
    set (S := usp - 128) in *. set (MV := mrestrict (ahid A model) M) in *. set (can := vals_ev vals 3).
    assert (HS16 : S mod 16 = 0).
    { unfold S. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hal. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct (dg_machine_pre scfg L ar C IL HI HIok sp0 Hsp DL Hdg M0 fdata vals kn LB LK cr A M model can S HK OKb P0 eq_refl D ltac:(unfold S; lia) ltac:(unfold S; lia) HS16)
      as (HW & HD & HIMG & HSTK & HC).
    assert (HFMT : L5KnA.L5KA.zeros_at MV 2147462296 16).
    { intros i Hi. apply (img_sh0 scfg L ar IL HI ICok sp0 DL M0 _ _ _ _ _ _ 91328 128 _ D); [lia | lia | lia | | lia].
      rewrite (aicl_poison IL ILY). repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    destruct (str_cstr scfg L ar C IL HI HIok sp0 Hsp DL M0 _ _ _ _ _ _ p0 a0s D (proj1 PLO) (proj2 PLO) STR NONUL PDEF) as (t8 & HSTR).
    pose proof (str_hull L ar IL HI sp0 Hsp DL M0 _ _ _ _ _ _ (bv_unsigned p0) (Z.of_nat (length a0s)) D SAH (proj1 PLO) ltac:(lia)) as HSH.
    destruct (str_statics scfg L ar C IL HI HIok sp0 Hsp DL Hdg Hdgs M0 _ _ _ _ _ _ D HIMG) as (HSN & HMC).
    assert (G12 : getr R 12%bv = Z_to_bv 64 (bv_unsigned p0)) by (rewrite G12p; symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hp : S <= bv_unsigned p0 /\ bv_unsigned p0 + Z.of_nat (length a0s) + 1 + 9 <= 2 ^ 47) by (unfold S; lia).
    set (mm := fun k => bv_unsigned (fr k)).
    assert (Hm : (0 <= mm 64 < 2 ^ 64 /\ 0 <= mm 72 < 2 ^ 64 /\ 0 <= mm 80 < 2 ^ 64 /\ 0 <= mm 88 < 2 ^ 64) /\ (0 <= mm 96 < 2 ^ 64 /\ 0 <= mm 104 < 2 ^ 64 /\ 0 <= mm 112 < 2 ^ 64 /\ 0 <= mm 120 < 2 ^ 64))
      by (unfold mm; repeat split; apply u64_range).
    assert (CELL : forall k, In k [64; 72; 80; 88; 96; 104; 112; 120] -> u64A MV (S + (128 - k)) (mm k)).
    { intros k Hk. unfold L5Defs.L5.u64_at, mm. rewrite Z_to_bv_bv_unsigned. replace (S + (128 - k)) with (usp - k) by (unfold S; lia). exact (FRK k Hk). }
    assert (HMF : u64A MV (S + 72) 1275136 /\ u64A MV (S + 64) (mm 64) /\ u64A MV (S + 56) (mm 72) /\ u64A MV (S + 48) (mm 80) /\ u64A MV (S + 40) (mm 88)
                  /\ u64A MV (S + 32) (mm 96) /\ u64A MV (S + 24) (mm 104) /\ u64A MV (S + 16) (mm 112) /\ u64A MV (S + 8) (mm 120)).
    { split; [unfold L5Defs.L5.u64_at; replace (S + 72) with (usp - 56) by (unfold S; lia); exact FRA|].
      split; [exact (CELL 64 ltac:(cbn [In]; tauto))|]. split; [exact (CELL 72 ltac:(cbn [In]; tauto))|]. split; [exact (CELL 80 ltac:(cbn [In]; tauto))|].
      split; [exact (CELL 88 ltac:(cbn [In]; tauto))|]. split; [exact (CELL 96 ltac:(cbn [In]; tauto))|]. split; [exact (CELL 104 ltac:(cbn [In]; tauto))|].
      split; [exact (CELL 112 ltac:(cbn [In]; tauto)) | exact (CELL 120 ltac:(cbn [In]; tauto))]. }
    destruct (Z_le_gt_dec (Z.of_nat (length a0s)) 66) as [HnA|HnA'].
    - apply (die_of_chainU [Na0DiagGlue.DG.PRE7 ++ a0s ++ Na0DiagGlue.DG.SUF7] _ vals kn LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
      + cbn [concat]. rewrite app_nil_r. apply msg_usage_eqA.
      + exact (usage_chainA fxq R MV S (bv_unsigned can) (bv_unsigned p0) a0s t8 G1 G2 G4 G10 G11 G8 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                 (u64_range can) HC HSN HMC _ _ _ _ _ _ _ _ Hm HMF HnA).
    - destruct (Z_le_gt_dec (Z.of_nat (length a0s)) 73) as [HnB|HnB'].
      + apply (die_of_chainU [(Na0DiagGlue.DG.PRE7 ++ a0s) ++ Na0DiagGlue.DG.SUF7; []] _ vals kn LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
        * cbn [concat]. rewrite !app_nil_r, <- app_assoc. apply msg_usage_eqA.
        * exact (usage_chainB fxq R MV S (bv_unsigned can) (bv_unsigned p0) a0s t8 G1 G2 G4 G10 G11 G8 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                   (u64_range can) HC HSN HMC _ _ _ _ _ _ _ _ Hm HMF ltac:(lia)).
      + apply (die_of_chainU [Na0DiagGlue.DG.PRE7 ++ a0s; Na0DiagGlue.DG.SUF7] _ vals kn LB LK cr A M model fxq R fs S HK OKb P0 D EFS FD2 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16).
        * cbn [concat]. rewrite !app_nil_r, <- app_assoc. apply msg_usage_eqA.
        * exact (usage_chainC fxq R MV S (bv_unsigned can) (bv_unsigned p0) a0s t8 G1 G2 G4 G10 G11 G8 G12 ltac:(unfold S; lia) ltac:(unfold S; lia) HS16 HW HD HIMG Hp HSTR HSH HSTK HFMT
                   (u64_range can) HC HSN _ _ _ _ _ _ _ _ Hm HMF ltac:(lia)).
  Qed.
End Arm.
End FPX_1.
End NraDiagArmUsage.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence. From LinuxProcessSemantics.Riscv Require Prelude Instr. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraArtHandoffK NraArtHandoffInstK NraStkShK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.
Module NraUsageEntry.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0HandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3SoundK AsanPlanSoundK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0043.AgentLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AxSymExec3K OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3SoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanCoreK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0076.AsanPlanK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSoundK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.AsanInitK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DefsK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0PlanImagesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0StartupK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBridgeK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffBInvK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0132.HandoffRolesK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0HandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_0 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0HSK_1 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0107.Na0MainTableK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0HandoffInstK.Na0HandoffInstK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0117.Na0DrvEntryK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0UsageEntryK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0StartupFinalK.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraArtHandoffK NraArtHandoffInstK NraStkShK. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraMainPhaseA. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcctShape OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceANull OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0035.ArtRuns OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0109.ArtBridge OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145.NarFsInv OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraArtHandoffK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraArtHandoffInstK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraStkShK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0077.Na0DrvEntryInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvRead OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvE OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraMainPhaseA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvMain OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmRefuse.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.ShapeLaws OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.BigintSpec.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.HeapIfaceAMxI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.StrictOfBI.      (* [comment removed for export] *)
Require Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Na0CertK_202.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0002. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0003.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0023.
Ltac2 kr_t_NraUsageEntry () := "C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes6lengthC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List=app_nth2_plusC47Corelib4Init5Peano2ltK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib7Mh_01058SymDrive9junk_valsC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC47Corelib5Lists7ListDef3nthK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z6of_natC49OSSVerify5KrLib8PropExec4getrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C47Corelib5Lists7ListDef3seqC47Corelib5Lists7ListDef3mapC59OSSVerify5KrLib7Mh_01058SymDrive;nth_map_seqC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init3Nat3addC47Corelib4Init9Datatypes3appC59OSSVerify5KrLib7Mh_01056SymRun7vals_evC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX23env01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX22evC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C49OSSVerify5KrLib8PropExec5v_addC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4ZdivAZplus_mod_idemp_rC49OSSVerify5KrLib8PropExec=bv_wrap64_modC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions@Z_to_bv_unsignedC4ELinuxProcessSemantics5Riscv3Sem5alu64C49OSSVerify5KrLib8PropExec7alu_addC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry3spxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26edenotC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K4ELinuxProcessSemantics5Riscv5Instr5aluop01K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr01C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3mulC46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums1Z03c59OSSVerify5KrLib7Mh_0266=NraUsageEntry8spx_valUC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK69OSSVerify5KrLib7Mh_00638SymExec23SX24expr02C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib7Mh_0119;Na0DrvEntryAregs_ok_by_indexAC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib7Mh_0266=NraUsageEntry8ev_junkUC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula08I69OSSVerify5KrLib7Mh_00638SymExec23SX24expr00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry8sr_mainUC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega=RingMicromega3Op203K69OSSVerify5KrLib7Mh_00638SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib=SymExec2Sound4SX2S7u_smallC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry;adenot_flatC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry:estart_spUC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib5Lists7ListDef6Forall00C46Stdlib5Lists4List=Forall_forallC46Stdlib5Lists4List<nth_error_InC47Corelib4Init5Logic5proj1C59OSSVerify5KrLib=SymExec2Sound4SX2S9kentry_okC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry05C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry06C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry07C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry04C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okI46Stdlib;setoid_ring<Ring_polynom5PExpr00K46Stdlib;setoid_ring<Ring_polynom5PExpr04K46Stdlib;setoid_ring<Ring_polynom5PExpr03K46Stdlib;setoid_ring<Ring_polynom5PExpr06K46Stdlib;setoid_ring<Ring_polynom5PExpr05I46Stdlib;setoid_ring<Ring_polynom3Pol00C46Stdlib;setoid_ring<Ring_polynom3PeqC46Stdlib;setoid_ring:ZArithRing>Zr_ring_lemma1I47Corelib4Init5Peano2le00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses9and_morphC59OSSVerify5KrLib7Mh_01059SymDriveX;adenot_lit0C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9nth_errorK47Corelib5Lists7ListDef6Forall01K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula05C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C46Stdlib;setoid_ring<Ring_polynom>mk_monpol_listC46Stdlib;setoid_ring<Ring_polynom:norm_substC46Stdlib9micromega;ZifyClasses6mkapp2K47Corelib5Lists7ListDef6Forall02C59OSSVerify5KrLib7Mh_0119;Na0DrvEntry9XC9_CELLSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrImgMTgt_fuzz_msgpack_encoder_asan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3oppC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z7quotremC46Stdlib;setoid_ring8Ring_tac@ring_subst_niterC56Stdlib6ZArith4Znat5Nat2Z6inj_lec59OSSVerify5KrLib7Mh_0266=NraUsageEntry8kn_mainUC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init5Logic4True01I46Stdlib;setoid_ring<Ring_polynom3Mon00C46Stdlib9micromega8ZifyInst7Inj_Z_ZC59OSSVerify5KrLib7Mh_0077>Na0UsageEntryK7tid_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01078Na0HSK_04HS_0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01078Na0HSK_14HS_1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK3HSAC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry9tid_chk_0C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry9tid_chk_1C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC59OSSVerify5KrLib7Mh_01329AsanInitK5SINV0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5argH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK6as0_A0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK;as0_chk_HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK7as0_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst;drv_chk_HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK7drv_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst;stk_chk_HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK7stk_chkC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK<as0_inst_budC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_eagerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK8a_abytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct7A_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstK<as0_inst_gapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK7a_totszC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC69OSSVerify5KrLib7Mh_00769AsanPlanK3APK6a_mapsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK9ent_guardC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib7Mh_0266=NraUsageEntry;tid_chk_HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077>Na0UsageEntryK8entg_tidC1?~~~~~~~~~~~~~~~C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run?total_arg_bytesC47Corelib4Init5Logic3notC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei>path_has_slashC4ELinuxProcessSemantics?LinuxProcessSem2Fs8path_eqbC46Stdlib5Lists4List2tlC59OSSVerify5KrLib7Mh_0077>Na0UsageEntryK9entg_str0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00387CatExec<cat_argv_ptrC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega7EnvRing5PExpr05C56Stdlib6ZArith6BinInt1Z9mod_smallC59OSSVerify5KrLib7Mh_0077>Na0UsageEntryK9entg_regsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry=main_regs_okUC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC59OSSVerify5KrLib7Mh_0077>Na0UsageEntryK@entg_stack_wordsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK:ent_windowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK7ent_imgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077?Na0DrvEntryInst:xc_chk_HSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK:ent_xcellsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry=main_know_okUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK6ent_lzC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK9ent_modelC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077>Na0UsageEntryK<entg_str0_hiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077>Na0UsageEntryKAentg_str0_definedC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib>AsanPlanSoundK4APSK5cs_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA4ahidC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct9mrestrictC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry:vals_mainUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA5lzinvC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsC59OSSVerify5KrLib7Mh_01178Na0DefsK6ASEGS0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01178Na0DefsK5ASAN0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01329AsanInitK5LIMITC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00769AsanPlanK3APK4amap00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK7fds_stdC1?~~~~~~~~~~~~~~~C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addI69OSSVerify5KrLib7Mh_0076;AxSymExec3K4AX2K3env00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C59OSSVerify5KrLib7Mh_01178Na0DefsK4APH0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00238AsanCeil>bottomup_floorC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX23env00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loC4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool02C6ELinuxProcessSemantics?LinuxProcessSem3Sys2Fs5Namei;dotdot_pathI69OSSVerify5KrLib7Mh_00769AsanPlanK3APK3acs00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0077>Na0UsageEntryKFentg_stack_defined_topC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface7definedC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX24expr03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA:kentry_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbC46Stdlib5Lists4List7forallbC59OSSVerify5KrLib7Mh_0250@NraDiagArmRefuse8dg_kn_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry3srUC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr;branch_cond02I69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry2rUC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry3knUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01267Na0DrvA4ENVAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry8usage_kAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01059SymDriveX@junk_vals_lengthC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_appC59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_lzinvC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX27scripts01C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00638SymExec23SX25carryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S8sc_denotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool=negb_true_iffC56Stdlib6ZArith6BinInt1Z7eqb_neqC69OSSVerify5KrLib7Mh_00638SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcctEsame_but_materializedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01058SymDrive8blobs_evC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:sub_blockAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6no_blsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01167DrvKitA8log_in_bC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib:dinv_blockC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib8ahid_sbmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib7sbm_fdsC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec4mkstC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C59OSSVerify5KrLib7Mh_00367SpinAlg9srealizesC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0116:As0DrvKitA:rz_run_lz2C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_00638SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs5FUELAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs6STOPSAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs8asegs_wxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368ShapeAlg4TSetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01267Na0DrvA4fds0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0119;Na0Drv_defs7IMG_W_AC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib5BMode;bm_off_instC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0063:BigintSpec4specC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec9msg_usageC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00634Spec5t_dieC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic9False_indC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC47Corelib4Init5Logic5proj2C49OSSVerify5KrLib=NraMainPhaseA6mp_budC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib=NraMainPhaseA6mp_gapC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK6as0_rnC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK6as0_arC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_noaccessC49OSSVerify5KrLibBNraArtHandoffInstKAas0_art_handoff_hC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK9as0_BASExC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK7as0_A0xC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6vml_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib?Na0HandoffInstK?Na0HandoffInstKBas0_handoff_staticC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117;Na0HandoffK7as0_RESC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7art_RESC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib=NraMainPhaseA;as0_RES_artC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib=NraMainPhaseA8mp_gap_hC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0117<Na0DrvEntryK7sp0_valC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv7art_gs0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_alloc_repC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv9art_fsinvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv5rn_HIC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_client_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_eager_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv:art_run_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_rt_staticsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_threadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv>art_rt_primaryC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_chunksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv:art_rt_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_rt_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_rt_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_rt_iaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_rt_blocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv<art_rt_ghostC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib=NraMainPhaseA3HIRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA9hl_img_hiC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ>asan_iface_okR00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB=rt_flag_in_fsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB9strict_okC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib=NraMainPhaseA3HIAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089<HeapIfaceAMx>asan_iface_okB00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfBCstrict_free_null_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089>HeapIfaceANull?afree_null_specC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:IcptIfaceA8aicpt_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00809StrictOfB=strict_of_nilC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ9strict_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6ri_invC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8ar_sptopC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0080:StrictOfBI;strict_icptC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01199Na0DrvLib;drv_layoutA00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK<as0_EXTRA_wfC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK9as0_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct4A_wfC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr04C49OSSVerify5KrLib>NraArtHandoffK3KSHC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry?as0_main_entryUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00368AsanAcct>H_off_segmentsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9m_vm_lazyC59OSSVerify5KrLib7Mh_00368AsanAcct:lazy_coverC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00368AsanAcct4MInv00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA7app_memC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0089<HeapIfaceAMx3HAJ;shadow_blkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface9lb_removeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_00849HeapIface<blocks_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA=fframes_apartC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA5ar_fsC1?~~~~~~~~~~~~~~~I35stdpp4base5NoDup00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA>shadow_allowedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA?ar_stack_bottomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<ar_stack_topC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK4botEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK2uEC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula07C56Stdlib6ZArith6BinInt1Z?add_mod_idemp_lC49OSSVerify5KrLib>NraArtHandoffK4topEC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntryGas0_main_stack_definedUC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01199Na0DrvLib6STKTOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<in_shadow_ofC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC49OSSVerify5KrLib9NraStkShK>as0_stksh_mainC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib9NraStkShKAas0_stksh_main_hiC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_01199Na0DrvLib4dinv01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib7Mh_0250:NraDrvMain8drv_ctxA01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0250:NraDrvMain8drv_ctxA00C1?~~~~~~~~~~~~~~~C46Stdlib6ZArith6Zorder9Zle_0_natK46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C59OSSVerify5KrLib7Mh_0116:As0DrvKitA@rdn_of_mrestrictC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic7f_equalK59OSSVerify5KrLib7Mh_0250:NraDrvMain9drv_pathA01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0250:NraDrvMain9drv_pathA00C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symc59OSSVerify5KrLib7Mh_0266=NraUsageEntry:drv_usageAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK2pcC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib=NraMainPhaseA6HSA_pcC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib7Mh_0266=NraUsageEntry;spec_usageAC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib=NraMainPhaseA:usage_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0076=AsanPlanCoreK4APCK2pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib>AsanPlanSoundK4APSK6cfg_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInvBart_handoff_targetC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01099ArtBridge=bridge_static00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01099ArtBridge4BINVC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv=art_credit_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv9art_kn_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv;art_lazy_okC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedC59OSSVerify5KrLib7Mh_01456NarInv5rn_arC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_01458NarFsInv7art_fsg00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01458NarFsInv8art_fsg0C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>NraArtHandoffK3K0DC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KCNTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00769AsanPlanK3APK5e_sp0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv6LENMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_01456NarInv4KMAXC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C59OSSVerify5KrLib7Mh_0089:HeapIfaceA8FS_BYTESC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I59OSSVerify5KrLib7Mh_01456NarInv7art_run00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA8asan_run00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA6fframeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_00357ArtRuns3aev00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asan_iface00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0089:HeapIfaceA<BIGSHADOW_LOC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib>AsanPlanSoundK>asanreflect_fxC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3fx0C1?~~~~~~~~~~~~~~~". Local Ltac lia := L5FastLiaT.plia1.
Import ListNotations.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import SX2. Import SX2S.

Definition sr_mainU : list expr :=
  [ELit 0; ELit 0x137500; spx (-48); ELit 0x10800; ELit 0x693b00; EVar 11; EVar 12; EVar 13;
   spx 8; EVar 2; EVar 2; spx 8; EVar 18; EVar 19; EVar 20; EVar 21;
   EVar 22; EVar 23; ELit 0xaea2c; EVar 25; ELit 0; ELit 0; ELit 0; ELit 0;
   ELit 0; ELit 0; ELit 0; ELit 0; EVar 34; EVar 35; EVar 36; EVar 37].

Definition kn_mainU : list kentry :=
  [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
   KWr (SA (EVar 0) (-6144513)) (6144513);
   KWord (SA (EVar 0) 8) 8 (EVar 1);
   KImg 0x10000 0x158000; KImg 0x6920d0 0x693a30;
   KImg 0x15b5a0 0x15b690; KImg 0x15b690 0x15b778; KImg 0x15b778 0x15c3a0;
   KWord (SA (ELit 0) 0x6b3b40) 8 (EVar 3);
   KWord (SA (ELit 0) 0x693a58) 4 (EVar 4); KRange (EVar 4) 1 4194303;
   KImg 0x15b4d0 0x15b578;
   KWord (SA (ELit 0) 7028080) 4 (ELit 0); KWord (SA (ELit 0) 7028115) 1 (ELit 0); KWord (SA (ELit 0) 7027552) 8 (ELit 7027560); KWord (SA (ELit 0) 7027544) 4 (ELit 1);
   KWord (SA (ELit 0) 7027568) 8 (ELit 1277044); KWord (SA (ELit 0) 7027824) 8 (ELit 648332); KWord (SA (ELit 0) 7027540) 4 (ELit 0); KWord (SA (ELit 0) 7027560) 8 (ELit 0);
   KWord (SA (ELit 0) 7029512) 8 (ELit 0); KWord (SA (ELit 0) 7027536) 1 (ELit 0); KWord (SA (ELit 0) 7028336) 4 (ELit 0)].      (* [comment removed for export] *)

Definition vals_mainU (sp p0 argcw can tid : word) (R : bvmap 5 word) : list word := [sp; p0; argcw; can; tid; Z_to_bv 64 0] ++ junk_vals R.

Section FPX_1. Context {fx : PropExec.FPState}.
Section PackU.
  (* [comment removed for export] *)
  Variables (sp : word) (argc envc STR0 : Z).
  Variable R : bvmap 5 word.
  Variable MV : word -> option byte.
  Variable ebs : nat -> list byte.
  #[local] Abbreviation usp := (bv_unsigned sp).
  Hypothesis Hsp : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0.
  Hypothesis Hb : 1 <= argc <= 1024 /\ 0 <= envc <= 256.
  Hypothesis REGS : forall r v, In (r, v)
    [(1, 0x137500); (2, usp - 48); (3, 0x10800); (4, 0x693b00); (8, usp + 8); (9, argc); (10, argc); (11, usp + 8);
     (12, usp + 16 + 8 * argc); (18, 0xaea2c); (19, usp + 16 + 8 * argc); (20, 0); (21, 0); (22, 0); (23, 0); (24, 0); (25, 0); (26, 0); (27, 0)] ->
    getr R (Z_to_bv 5 r) = Z_to_bv 64 v.
  Hypothesis WORD8 : rdn ASEGS MV (Z_to_bv 64 (usp + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 STR0)).
  Hypothesis WINDOW : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= stack_window_depth -> store_ok ASEGS MV (Z_to_bv 64 (usp - stack_window_depth + d)) m = true.
  Variable can : word.
  Hypothesis GUARD : rdn ASEGS MV (Z_to_bv 64 0x6b3b40) 8 = Some (word_to_le_bytes 8 can).
  Hypothesis IMG : forall lo hi i, In (lo, hi) [(0x10000, 0x158de8); (0x158e04, 0x15c3a0); (0x6820ca, 0x693a30); (0x6b3dc8, 0x6b3df8)] -> lo <= i < hi -> MV (Z_to_bv 64 i) = None.
  Variable tid : word.
  Hypothesis TIDR : 1 <= bv_unsigned tid <= 4194303.
  Hypothesis TIDW : rdn ASEGS MV (Z_to_bv 64 0x693a58) 4 = Some (word_to_le_bytes 4 tid).
  Hypothesis XCW : Forall (fun c : Z * nat * Z => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9_CELLS.

  Let p0 : word := Z_to_bv 64 STR0.
  Let ES : env := Env (vals_ev (vals_mainU sp p0 (Z_to_bv 64 argc) can tid R)) ebs.

  #[using="Type"] Lemma ev_junkU : forall i, (i < 32)%nat -> ev ES (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. unfold ES, vals_mainU. cbn [ev]. unfold vals_ev.
    change (6 + i)%nat with (length [sp; p0; Z_to_bv 64 argc; can; tid; Z_to_bv 64 0] + i)%nat. rewrite app_nth2_plus. unfold junk_vals.
    rewrite (nth_map_seq (fun i => getr R (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  #[using="Type"] Lemma spx_valU : forall k, edenot ES (spx k) = Z_to_bv 64 (usp + k).
  Proof.
    intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev ES 0) with sp.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  #[using="REGS"] Theorem main_regs_okU : regs_ok ES sr_mainU R.
Proof.
apply regs_ok_by_indexA. intros i Hi.
destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; cbn [nth sr_mainU Z.of_nat Pos.of_succ_nat Pos.succ].
all: try solve [rewrite ?spx_valU; cbn [edenot]; apply REGS; cbn [In]; repeat (first [left; reflexivity | right])].
all: try (match goal with |- getr R (Z_to_bv 5 ?z) = edenot ES (EVar _) =>
let k := eval cbv in (Z.to_nat z) in exact (eq_sym (ev_junkU k ltac:(lia))) end).
cbn [edenot]. reflexivity.
Qed.

  #[using="Type"] Lemma estart_spU : forall off, estart ES (SA (EVar 0) off) = usp + off.
Proof.
ltac2:(KReplay.run1 (kr_t_NraUsageEntry ()) ["FPX_1"; "PackU"] "h03offp;1p;2p;3g0049j10Tg004^j1;Tg00DAj21Tg00Dkj23Tg00:1j2:Tg00Yoj19Tg00o_j28Tg010`j15Tg00LWj26Tg011`j17Tg009Wj32Tg012_j24Tg00MWR0g00BK#0#0#0#0#0#0#;R1p,2sp'1f0R2'3R3,:0p,2ESR4g00Al#9/82R2#5'6,11%72'3=203e1442=203eW0o"). Qed.

  #[using="Hsp Hb WORD8 WINDOW GUARD IMG TIDR TIDW XCW"] Theorem main_know_okU : know_ok ASEGS ES MV kn_mainU.
Proof.
destruct Hsp as (S1 & S2). destruct Hb as (B1 & B2).
assert (FLIT : forall a n, 0 <= a -> 0 <= n -> a + n <= 2 ^ 63 -> flat ES (SA (ELit 0) a) n).
{ intros a n H1 H2 H3. unfold flat, estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. lia. }
assert (ALIT : forall a, 0 <= a < 2 ^ 63 -> adenot ES (SA (ELit 0) a) = Z_to_bv 64 a).
{ intros a Ha. rewrite (adenot_flat ES (SA (ELit 0) a) 0 ltac:(apply FLIT; lia)). unfold estart. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia. reflexivity. }
assert (FL : forall off n, -8388608 <= off -> 0 <= n -> off + n <= 4096 -> flat ES (SA (EVar 0) off) n).
{ intros off n H1 H2 H3. unfold flat. rewrite estart_spU. lia. }
assert (XC : forall (i : nat) c, nth_error XC9_CELLS i = Some c ->
rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c))))
by (intros i c Hn; exact (proj1 (Forall_forall _ _) XCW c (nth_error_In _ _ Hn))).
unfold kn_mainU, know_ok. repeat (apply Forall_cons); [ .. | apply Forall_nil]; cbn [kentry_ok].
- split; [lia | exact S2].
- cbn [edenot]. change (ev ES 0) with sp. lia.
- split; [apply FL; lia|]. intros d m Hd Hm. rewrite estart_spU.
assert (SWD : stack_window_depth = 6144513) by (vm_compute; reflexivity). rewrite SWD in WINDOW.
replace (usp + -6144513 + d) with (usp - 6144513 + d) by ring. apply WINDOW; assumption.
- split; [lia|]. split; [apply FL; lia|]. rewrite (adenot_flat ES (SA (EVar 0) 8) 8 ltac:(apply FL; lia)), estart_spU. exact WORD8.
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x10000 0x158de8); [left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x6820ca 0x693a30); [right; right; left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small 0) by lia; lia|].
rewrite adenot_lit0. exact GUARD.
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact TIDW.
- cbn [edenot]. change (ev ES 4) with tid. lia.
- split; [lia|]. split; [lia|]. intros i Hi. apply (IMG 0x158e04 0x15c3a0); [right; left; reflexivity | lia].
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 0%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 1%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 2%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 3%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 4%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 5%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 6%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 7%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 8%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 9%nat _ eq_refl).
- split; [lia|]. split; [apply FLIT; lia|]. rewrite ALIT by lia. exact (XC 10%nat _ eq_refl).
Qed.
End PackU.
End FPX_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma tid_chk_HSA : forall r h, (h < 2)%nat -> tid_chk (HSA r h) = true.
Proof. intros r [|[|h]] H; [| |lia]; unfold HSA; destruct (Z.eqb r 1); vm_compute; reflexivity. Qed.

Section FPX_2. Context {fx : PropExec.FPState}.
Section InstU.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variable argv envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  (* [comment removed for export] *)
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.   (* the SIGPIPE disposition at exec, free at LPS 727298f3 *)
  Variable apc : N.
  (* [comment removed for export] *)
  Variable r : Z.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis Hvl : valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis HRZ : r = APK.rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))).
  Remark r01 : 0 <= r <= 1.
  Proof. rewrite HRZ. apply APK.rseq_z_range. Qed.
  #[local] Abbreviation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Abbreviation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Abbreviation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461477888 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665413120 + BUDGET) + (23 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  #[local] Abbreviation usp := (bv_unsigned sp).
  #[local] Abbreviation argc := (Z.of_nat (length argv)).
  #[local] Abbreviation envc := (Z.of_nat (length envp)).
  #[local] Abbreviation a0s := (nth 0 argv []).
  #[local] Abbreviation STR0 := (usp + Z.of_nat (cat_string_off (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))) sp (ed_top rdraw) argv envp execfn)).

  Theorem as0_main_entryU : forall ebs h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    let A0 := as0_A0 EXTRA (HSA r h) E in
    let MV := mrestrict (ahid A0 model) FULL in
    let p0 := Z_to_bv 64 STR0 in
    exists can tid : word,
      let ES := Env (vals_ev (vals_mainU sp p0 (Z_to_bv 64 argc) can tid R)) ebs in
      SX2S.regs_ok ES sr_mainU R
      /\ SX2S.know_ok ASEGS ES MV kn_mainU
      /\ lzinv ASEGS (ahid A0 model) A0 model
      /\ m_fds model = APSK.fds_std /\ m_fs model = fs
      /\ rdn ASEGS MV p0 (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])
      /\ bv_unsigned p0 = STR0
      /\ bv_unsigned p0 + Z.of_nat (length a0s) + 1 + 9 <= 2 ^ 47
      /\ (forall i, 0 <= i < Z.of_nat (length a0s) + 1 + 8 -> FULL (Z_to_bv 64 (bv_unsigned p0 + i)) <> None).
  Proof using All.
    intros ebs h Hh E R FULL model HC A0 MV p0.
    pose proof (as0_chk_HSA r h Hh) as C0. pose proof (drv_chk_HSA r h r01 Hh) as CD. pose proof (stk_chk_HSA r h r01 Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le r h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP r h Hh) as GP.
    assert (G : exists can : word, rdn ASEGS MV (Z_to_bv 64 0x6b3b40) 8 = Some (word_to_le_bytes 8 can)).
    { edestruct (ent_guard sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc) as (can & G1 & G2); [ .. | exists can; exact G1]; eassumption. }
    destruct G as (can & G1). exists can.
    assert (T : exists tid : word, 1 <= bv_unsigned tid <= 4194303 /\ rdn ASEGS MV (Z_to_bv 64 0x693a58) 4 = Some (word_to_le_bytes 4 tid)).
    { eapply (entg_tid sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption. exact (tid_chk_HSA r h Hh). }
    destruct T as (tid & TR & T2). exists tid. cbv zeta.
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0).
    { destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in H1, H2. lia. }
    assert (HB : 1 <= argc <= 1024 /\ 0 <= envc <= 256).
    { pose proof Hve as [Hle _]. pose proof Hva as (Hac & _). lia. }
    assert (STR : rdn ASEGS MV (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) (length a0s + 1) = Some (a0s ++ [Z_to_bv 8 0])
                  /\ bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp execfn 0) = STR0).
    { eapply (entg_str0 sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption. }
    destruct STR as (STR1 & PV0).
    assert (PE : p0 = cat_argv_ptr (ed_top rdraw) argv envp execfn 0).
    { unfold p0. rewrite <- PV0. apply Z_to_bv_bv_unsigned. }
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    - apply (main_regs_okU sp argc STR0 R ebs).
      eapply (entg_regs sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption.
    - apply (main_know_okU sp argc envc STR0 R MV ebs SR HB).
      + eapply proj2. eapply (entg_stack_words sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption.
      + eapply (ent_window sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); eassumption.
      + exact G1.
      + eapply (ent_img sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); eassumption.
      + exact TR.
      + exact T2.
      + change XC9_CELLS with XC9K. eapply (ent_xcells sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption; first [reflexivity | exact (xc_chk_HSA r h r01 Hh)].
    - unfold lzinv. eapply (ent_lz sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); eassumption.
    - rewrite PE. exact STR1.
    - rewrite PE. exact PV0.
    - rewrite PE. eapply (entg_str0_hi sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption.
    - rewrite PE. eapply (entg_str0_defined sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption.
  Qed.

  Theorem as0_main_stack_definedU : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    forall top, top mod 4096 = 0 -> top <= usp + 4096 -> defined FULL usp (top - usp).
  Proof using All.
    intros h Hh E R FULL model HC top Hm Hle i Hi.
    pose proof (as0_chk_HSA r h Hh) as C0. pose proof (drv_chk_HSA r h r01 Hh) as CD. pose proof (stk_chk_HSA r h r01 Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le r h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP r h Hh) as GP.
    eapply (entg_stack_defined_top sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption.
  Qed.
End InstU.
End FPX_2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX_3. Context {fx : PropExec.FPState}.
Definition rU := Eval vm_compute in runA (SCR [true] [] []) (SS 0xaea2c sr_mainU [] kn_mainU 38).
Definition srU : list expr := Eval vm_compute in s_regs (fst (fst rU)).
Definition knU : list kentry := Eval vm_compute in kn_after rU kn_mainU.
End FPX_3.

(* [comment removed for export] *)
Lemma usage_itinerary_okA :
  (s_pc (fst (fst rU)), snd (fst rU)) = (0x6a2e4, [SCBr true BC_NE (EVar 2) (ELit 2)])
  /\ (nth 1 srU (ELit 0), nth 2 srU (ELit 0), nth 4 srU (ELit 0), nth 8 srU (ELit 0), nth 10 srU (ELit 0), nth 11 srU (ELit 0), nth 12 srU (ELit 0))
     = (ELit 715744, EAlu ALU_ADD (EVar 0) (ELit (-128)), ELit 6896384, ELit 2, ELit 1422752, ELit 91345, EVar 1)
  /\ forallb (fun K => existsb (kentry_eqb K) knU)
       [KWord (SA (EVar 0) (-56)) 8 (ELit 1275136); KWord (SA (EVar 0) (-64)) 8 (EAlu ALU_ADD (EVar 0) (ELit 8)); KWord (SA (EVar 0) (-72)) 8 (EVar 2);
        KWord (SA (EVar 0) (-80)) 8 (ELit 715308); KWord (SA (EVar 0) (-88)) 8 (EVar 25); KWord (SA (EVar 0) (-96)) 8 (ELit 0); KWord (SA (EVar 0) (-104)) 8 (ELit 0);
        KWord (SA (EVar 0) (-112)) 8 (ELit 0); KWord (SA (EVar 0) (-120)) 8 (ELit 0); KWord (SA (EVar 0) 8) 8 (EVar 1)] = true
  /\ dg_kn_ok knU = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Section FPX_4. Context {fx : PropExec.FPState}.
Variable scfg : SpuriousCfg.
Section Usage.
  Variable L : asan_layout.
  Variable ar : asan_run.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable HI : asan_iface.
  Hypothesis HIok : asan_iface_okB L ar C scfg HI.
  Variable sp0 : word.
  Hypothesis Hsp : 0x7fff80000000 <= bv_unsigned sp0 <= 2 ^ 47.
  Hypothesis DL : drv_layoutA L ar IL sp0.
  Variable fs0 : Fs.Fs.
  Variables p0 can : word.
  Variable M0 : word -> option byte.
  Variable LK0 : list fframe.
  Variable cr0 : credit.
  Variable A0 : list (Z * Z).

  #[local] Abbreviation dinvA := (dinv ar HI sp0 M0).
  #[local] Abbreviation ENV0 := (ENVA []).

  (* [comment removed for export] *)
  Definition usage_kA (KU : TSet) : Prop :=
    forall vals R M (model : Model),
      length vals = 38%nat -> vals_ev vals 0 = sp0 -> vals_ev vals 1 = p0 -> vals_ev vals 3 = can ->
      regs_ok (ENV0 vals) srU R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model) M) knU ->
      dinvA [] LK0 cr0 A0 M model -> m_fds model = fds0 -> m_fs model = fs0 ->
      srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0x6a2e4) M (seg_rom ASEGS)) model) KU.

  #[using="L C IL HIok Hsp DL"] Theorem drv_usageA : forall KU R (model : Model) (argcw tid : word),
    let vals := vals_mainU sp0 p0 argcw can tid R in
    bv_unsigned argcw <> 2 ->
    regs_ok (ENV0 vals) sr_mainU R -> know_ok ASEGS (ENV0 vals) (mrestrict (ahid A0 model) M0) kn_mainU ->
    dinvA [] LK0 cr0 A0 M0 model -> m_fds model = fds0 -> m_fs model = fs0 ->
    usage_kA KU ->
    srealizes ASEGS scfg (mkCfg (mkst R (Z_to_bv 64 0xaea2c) M0 (seg_rom ASEGS)) model) KU.
Proof.
intros KU R model argcw tid vals Hargc HR HK DI Hfds Hfs0 HKU.
pose proof Hsp as Hsp'.
assert (HL : length vals = 38%nat) by (subst vals; unfold vals_mainU; rewrite length_app, junk_vals_length; reflexivity).
assert (P0 : vals_ev vals 0 = sp0) by reflexivity.
assert (P1 : vals_ev vals 1 = p0) by reflexivity.
assert (P2 : vals_ev vals 2 = argcw) by reflexivity.
assert (P3 : vals_ev vals 3 = can) by reflexivity.
clearbody vals.
drv_block0 HIok Hsp DL HR HK DI P0 (SCR [true] [] []) 38%nat.
{ unfold sc_denot, LinuxProcessSemantics.Riscv.Sem.branch_taken. cbn [edenot ev ENVA]. rewrite P2. unfold bv_eqb.
apply negb_true_iff, Z.eqb_neq. change (bv_unsigned (Z_to_bv 64 2)) with 2. exact Hargc. }
destruct (sbm_fds _ _ SBM) as (F1 & F2). rewrite Hfds in F1. rewrite Hfs0 in F2.
lazymatch goal with |- srealizes _ _ (mkCfg (mkst ?Rc _ ?Mc _) ?mc) _ => apply (HKU vals Rc Mc mc) end; try assumption.
Qed.
End Usage.
End FPX_4.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition dg_usage_stmt (scfg : SpuriousCfg) (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) : Prop :=
  forall ar HI sp0 M0, drv_ctxA scfg L C IL ar HI sp0 M0 -> forall a0s fs0 p0 can cr0 A0, drv_pathA sp0 M0 p0 a0s ->
    shadow_allowed A0 (ahl_ceil ar) (2 ^ 47 - ahl_ceil ar) ->
    usage_kA scfg ar HI sp0 fs0 p0 can M0 [] cr0 A0 (t_die (msg_usage a0s) fs0).

Lemma spec_usageA : forall argv fs, length argv <> 2%nat -> spec argv fs = t_die (msg_usage (nth 0 argv [])) fs.
Proof. intros argv fs H. destruct argv as [|a [|b [|c l]]]; try reflexivity. exfalso. apply H. reflexivity. Qed.

Section UsagePhase.
  Variable scfg : SpuriousCfg.
  Variable L : asan_layout.
  Variable C : asan_statics_cells.
  Variable IL : icpt_layout.
  Variable BUDGET : Z.
  Hypothesis BUD_ge : 2 ^ 36 + 2 ^ 20 + NarInv.PRIMCAP <= BUDGET.
  Hypothesis BUD_hi : BUDGET <= 2 ^ 39 - 2 ^ 35.
  Hypothesis INST_OK : inst_ok_stmt scfg L C BUDGET.
  Hypothesis FREE_NULL : free_null_stmt scfg L BUDGET.
  Hypothesis H4E : h4e_stmt BUDGET.
  Hypothesis ICPT_OK : icpt_ok_stmt scfg L IL BUDGET.
  Hypothesis DLA_OK : dla_ok_stmt scfg L C IL.
  Hypothesis DRV_CONSTS : drv_consts_stmt L C IL.
  Hypothesis DG_USAGE : dg_usage_stmt scfg L C IL.

  #[using="L C IL BUDGET BUD_ge BUD_hi INST_OK FREE_NULL H4E ICPT_OK DLA_OK DRV_CONSTS DG_USAGE"] Theorem as0_usage : usage_stmt scfg.
  Proof.
  unfold usage_stmt. intros sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hvfs Hlau Hvl HRZ h Hh2 E R FULL model HC Hargc.
  assert (r01 : 0 <= r <= 1) by (rewrite HRZ; apply APK.rseq_z_range).
  assert (EFS : m_fs model = fs).
  (* [DrvEntryK]'s [drv_chk_parts] proves its [OE] with a bare [subst], which
  rewrites with that Section's [HRZ]; so [ent_model] and [sp0_val], which use
  [drv_chk_parts], take [HRZ] (after [r], resp. after [Hlau]). *)
  { exact (proj2 (ent_model sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r HRZ (HSA r h) (drv_chk_HSA r h r01 Hh2) E R FULL model HC)). }
  rewrite (spec_usageA argv fs Hargc).
  pose proof (mp_bud BUDGET BUD_ge) as MPB. pose proof (mp_gap BUDGET BUD_hi) as MPG.
  set (cs := HSA r h). set (rn := as0_rn E cs). set (ar := as0_ar E cs).
  set (MAPS0 := vm_maps (m_vmmaps model)). set (RESV0 := vm_reserved (m_vmmaps model)). set (NOACC0 := vm_noaccess (m_vmmaps model)).
  pose proof (as0_art_handoff_h sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau BUDGET BUD_ge BUD_hi r h Hh2 E R FULL model HC) as HT.
  pose proof (as0_handoff_static sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX MPB MPG r h Hh2 E R FULL model HC) as BS.
  rewrite (as0_RES_art r h Hh2 E) in BS. fold cs rn in BS.
  (* [comment removed for export] *)
  pose proof (sp0_val sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX (HSA r h) (drv_chk_HSA r h r01 Hh2) (mp_gap_h BUDGET BUD_hi r h Hh2)
  E R FULL model HC) as SPV.
  pose proof HT as (REP & _ & _ & _ & CLI & _). destruct REP as (ROK & _).
  set (HR0 := HIR BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn).
  assert (INSTR : hl_img_hi L <= BIGSHADOW_LO /\ HAJ.asan_iface_okR L ar C scfg HR0 /\ rt_flag_in_fs L ar HR0).
  { apply (INST_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  destruct INSTR as (IMGL & HIRok & FLG).
  assert (HIok : asan_iface_okB L ar C scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)) by exact (strict_ok L ar C scfg HR0 IMGL FLG HIRok).
  assert (FNok : afree_null_spec L ar scfg (HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn)).
  { apply (strict_free_null_of L ar C scfg HR0 HIRok). apply (FREE_NULL MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  assert (ICR : aicpt_ok L ar IL scfg HR0).
  { apply (ICPT_OK MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn); [exact BS | exact ROK | reflexivity | reflexivity | reflexivity | reflexivity]. }
  pose proof (strict_of_nil HR0 _ _ _ _ (H4E _ _ _ _ _ _ _ _ _ _ _ _ HT)) as RI.
  set (HI := HIA BUDGET MAPS0 RESV0 NOACC0 (as0_BASEx cs E) rn) in *.
  change (HAJ.strict_of HR0) with HI in RI.
  assert (SPT : ar_sptop ar = bv_unsigned sp) by exact SPV.
  assert (ICok : aicpt_ok L ar IL scfg HI) by exact (strict_icpt L ar C IL scfg HR0 IMGL HIRok ICR).
  pose proof (DLA_OK ar HI sp HIok SPT) as DL.
  pose proof (as0_EXTRA_wf cs E) as XWF.
  assert (XBL : 16515072 + 2461477888 + A_bytes (as0_EXTRA cs E) + BUDGET <= Mh_0132.AsanInitK.LIMIT).
  { unfold as0_EXTRA. cbn [A_bytes fst snd]. unfold Mh_0132.AsanInitK.LIMIT, target_alloc_limit. lia. }
  destruct (as0_main_entryU sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX MPB (as0_EXTRA cs E) XWF XBL MPG
  (blobs_ev [[]; []; []; []; []]) h Hh2 E R FULL model HC) as (can & tid & HR & HK & LZ & FDS & _ & STR & PV & PH & PDEF).
  pose proof LZ as (HOFF & _ & _ & MI & HALT).
  destruct CLI as (_ & _ & SAH & _ & S1 & S2 & S3 & S4 & S5 & _).
  cbn [as0_rn rn_ar as0_ar ar_stack_top ar_stack_bottom ar_sptop] in S1, S2, S3, S4, S5.
  assert (SDEF : defined FULL (bv_unsigned sp) (ar_stack_top ar - bv_unsigned sp)).
  { apply (as0_main_stack_definedU sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc r Hsp Hva Hve Hfit Hlau Hvl HRZ BUDGET Mh_0145.NarInv.LENMAX Mh_0145.NarInv.KMAX MPB (as0_EXTRA cs E) XWF XBL MPG
  h Hh2 E R FULL model HC); unfold ar, cs; cbn [as0_ar ar_stack_top]; rewrite SPV in *.
  - rewrite S5. rewrite <- Z.add_mod_idemp_l by lia. rewrite S3. reflexivity.
  - lia. }
  assert (DI : dinv ar HI sp FULL [] [] (Mh_0145.NarInv.KCNT, 2 ^ 36) (as0_A0x cs E) FULL model).
  { apply DINV; [exact RI | exact MI | exact HALT | reflexivity | | | exact (APSK.co_rdr _ _ _ _ _ _ _ _ _ _ _ HC)].
  intros x Hx. apply (as0_stksh_main sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau r h Hh2 E R FULL model HC). unfold STKTOP, ar, cs in Hx. cbn [as0_ar ar_sptop ar_stack_top] in Hx. rewrite SPV in Hx. exact Hx.
  intros x Hx. apply (as0_stksh_main_hi sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc Hsp Hva Hve Hfit Hlau r h Hh2 E R FULL model HC). unfold ahl_ceil, ar, cs in Hx. cbn [as0_ar ar_sptop] in Hx. rewrite SPV in Hx. exact Hx. }
  assert (SR : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
  assert (SA16 : bv_unsigned sp mod 16 = 0) by (destruct Hsp as (_ & _ & H3); exact H3).
  assert (HAC : 1 <= Z.of_nat (length argv) <= 1024) by (destruct Hva as (Hac & _); exact Hac).
  (* [comment removed for export] *)
  set (p0 := Z_to_bv 64 (bv_unsigned sp + Z.of_nat (cat_string_off (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))) sp (ed_top rdraw) argv envp execfn))) in *.
  set (a0s := nth 0 argv []) in *.
  assert (CTX : drv_ctxA scfg L C IL ar HI sp FULL) by (constructor; assumption).
  assert (PTH : drv_pathA sp FULL p0 a0s).
  { constructor.
  - rewrite PV. pose proof (Zle_0_nat (length envp)). lia.
  - exact (rdn_of_mrestrict ASEGS _ FULL HOFF _ _ _ STR).
  - destruct Hva as (_ & _ & _ & Hnn & _). unfold a0s. destruct argv as [|a l]; [cbn in HAC; lia|]. inversion Hnn as [|x l' Hx _]; subst. exact Hx.
  - destruct Hva as (_ & _ & Hfa & _). unfold a0s. destruct argv as [|a l]; [cbn in HAC; lia|]. inversion Hfa as [|x l' Hx _]; subst. exact Hx.
  - intros i Hi. exact (PDEF i Hi). }
  unfold APSK.cfg_of, cs. rewrite (HSA_pc r h Hh2). fold cs.
  apply (@drv_usageA PropExec.fx0 scfg L ar C IL HI HIok sp SR DL fs p0 can FULL [] (Mh_0145.NarInv.KCNT, 2 ^ 36) (as0_A0x cs E)
  (t_die (msg_usage a0s) fs) R model (Z_to_bv 64 (Z.of_nat (length argv))) tid).
  - rewrite u_small by lia. intros Hc. apply Hargc. lia.
  - exact HR.
  - exact HK.
  - exact DI.
  - exact FDS.
  - exact EFS.
  - exact (DG_USAGE ar HI sp FULL CTX a0s fs p0 can (Mh_0145.NarInv.KCNT, 2 ^ 36) (as0_A0x cs E) PTH SAH).
  Qed.
End UsagePhase.
End NraUsageEntry.
Module NraUsageArm.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Asan.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SymExec2Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require NraMainPhaseA. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0145. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.ShapeAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0036.SpinAlg OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.Spec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0063.SymExec2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SymExec2Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDrive OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0105.SymDriveX OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0116.As0DrvKitA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvEntry OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0Drv_defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvLib OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0119.Na0DrvStdio OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0126.Na0DrvA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvE2 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.NraMainPhaseA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDrvMain OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmRefuse OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagStrK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0250.NraDiagArmOpen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266.NraDiagArmUsage OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0266.NraUsageEntry.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Existing Instance PropExec.fx0.

Theorem dg_usage_ok : forall scfg L C IL, dg_usage_stmt scfg L C IL.
Proof.
  intros scfg L C IL ar HI sp0 M0 [HIok _ ICok (ILY & _ & _ & _ & _ & _ & HEX & HDG & HDGS & _) Hsp Hal DL _] a0s fs0 p0 can cr0 A0 [PLO STR NONUL PLEN PDEF] SAH.
  unfold usage_kA. intros vals R M model HL P0 P1 P3 HR HK DI F1 F2.
  destruct usage_itinerary_okA as (_ & _ & FRB & OKb).
  set (E := ENVA [] vals) in *.
  assert (FR : forall off v, existsb (kentry_eqb (KWord (SA (EVar 0) off) 8 v)) knU = true ->
               rdn ASEGS (mrestrict (ahid A0 model) M) (Z_to_bv 64 (bv_unsigned sp0 + off)) 8 = Some (word_to_le_bytes 8 (edenot E v))).
  { intros off v Hb. exact (kword_sp sp0 vals _ _ knU off 8 v HK Hb P0). }
  apply (dg_usage_site scfg L ar C IL HI HIok ICok ILY sp0 Hsp Hal DL HEX HDG HDGS M0 [] PropExec.fx0 vals knU R M model [] [] cr0 A0 fs0 p0 a0s
           (fun k => if Z.eqb k 64 then edenot E (EAlu ALU_ADD (EVar 0) (ELit 8)) else if Z.eqb k 72 then edenot E (EVar 2) else if Z.eqb k 80 then edenot E (ELit 715308)
                     else if Z.eqb k 88 then edenot E (EVar 25) else Z_to_bv 64 0) HK OKb P0).
  - regv HR (1%bv : reg). reflexivity.
  - regv HR (2%bv : reg). cbn [edenot ev ENVA E]. rewrite P0. apply alu_add_w_litA.
  - regv HR (4%bv : reg). reflexivity.
  - regv HR (8%bv : reg). reflexivity.
  - regv HR (10%bv : reg). reflexivity.
  - regv HR (11%bv : reg). reflexivity.
  - regv HR (12%bv : reg). cbn [edenot ev ENVA E]. exact P1.
  - exact DI.
  - exact F2.
  - rewrite F1. vm_compute. reflexivity.
  - exact (STR_ATA ar sp0 M0 A0 p0 a0s PLO STR NONUL PLEN PDEF SAH).
  - replace (bv_unsigned sp0 - 56) with (bv_unsigned sp0 + -56) by ring. exact (FR (-56) (ELit 1275136) eq_refl).
  - intros k Hk. cbn [In] in Hk.
    destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [Z.eqb Pos.eqb].
    + replace (bv_unsigned sp0 - 64) with (bv_unsigned sp0 + -64) by ring. exact (FR (-64) (EAlu ALU_ADD (EVar 0) (ELit 8)) eq_refl).
    + replace (bv_unsigned sp0 - 72) with (bv_unsigned sp0 + -72) by ring. exact (FR (-72) (EVar 2) eq_refl).
    + replace (bv_unsigned sp0 - 80) with (bv_unsigned sp0 + -80) by ring. exact (FR (-80) (ELit 715308) eq_refl).
    + replace (bv_unsigned sp0 - 88) with (bv_unsigned sp0 + -88) by ring. exact (FR (-88) (EVar 25) eq_refl).
    + replace (bv_unsigned sp0 - 96) with (bv_unsigned sp0 + -96) by ring. exact (FR (-96) (ELit 0) eq_refl).
    + replace (bv_unsigned sp0 - 104) with (bv_unsigned sp0 + -104) by ring. exact (FR (-104) (ELit 0) eq_refl).
    + replace (bv_unsigned sp0 - 112) with (bv_unsigned sp0 + -112) by ring. exact (FR (-112) (ELit 0) eq_refl).
    + replace (bv_unsigned sp0 - 120) with (bv_unsigned sp0 + -120) by ring. exact (FR (-120) (ELit 0) eq_refl).
Qed.

(* [comment removed for export] *)
Theorem as0_usage_closed : forall scfg (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (BUDGET : Z),
  2 ^ 36 + 2 ^ 20 + NarInv.PRIMCAP <= BUDGET -> BUDGET <= 2 ^ 39 - 2 ^ 35 ->
  inst_ok_stmt scfg L C BUDGET -> free_null_stmt scfg L BUDGET -> h4e_stmt BUDGET -> icpt_ok_stmt scfg L IL BUDGET -> dla_ok_stmt scfg L C IL -> drv_consts_stmt L C IL ->
  usage_stmt scfg.
Proof.
  intros scfg L C IL BUDGET B1 B2 INST FN H4 ICPT DLA CONSTS.
  exact (as0_usage scfg L C IL BUDGET B1 B2 INST FN H4 ICPT DLA CONSTS (dg_usage_ok scfg L C IL)).
Qed.

End NraUsageArm.
