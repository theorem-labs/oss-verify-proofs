(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BArr BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BxSymExec3Sound BxSymExec3B BothAcct BothPlanCore BothPlan BothPlanSound BothPlanSoundSums BothInit BothHexScan BsImages BsPlanImages BsHSTab BsStartupHSF BsMainVM BsMainState BsMainFacts BsMainLazyChk BsMainLazy BsMainCells BsMainIface BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsMainSyms.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BsMainIfaceAHM () := "K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainFacts<hole_grantedC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainFacts3XofC6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b05K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b04C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b06C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b08C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b09C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b10C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b11C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b12C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b13C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b16C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b20C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b21C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b22C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms6ps_b23C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms7ps_b19rC6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms>pm_region_infoK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedC6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms<pm_stack_topC6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms5pm_shC47Corelib4Init9Datatypes3sndC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainCells6cx_valC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface7pm_vmemK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2wzK7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell01K47Corelib4Init9Datatypes4list02C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib5BStep8rw_cellsK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z2leC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface=img_word_mainC47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainCells4csym00K6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainCells4csym03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsI7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib6BCells4cell00K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat02C6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface6kp_b05C6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface8kp_factsC56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms9page_downC56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib:BLiaTuning9zify_doneC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem2waC7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BacX2b8K47Corelib4Init9Datatypes6option01C6ARocqVerifyHarness?AgentSubmission3bpB5Start:BsMainSyms8pm_shortC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainCells<world_ok_allC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface6vm_objC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface9zero_mainC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00c6ARocqVerifyHarness?AgentSubmission3bpB5Start>BsMainIfaceAHM8ahm_geomC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainCells5w_allI47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib7BLFrame3stkC6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface8pd_factsK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c6ARocqVerifyHarness?AgentSubmission3bpB5Start>BsMainIfaceAHM8ahm_zeroK47Corelib4Init5Logic2ex01C6ARocqVerifyHarness?AgentSubmission3bpB5Start;BsMainIface;stk_of_someK46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01".
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk ASEGS brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Vfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Hh : HSF_asan h = Some ch.
  Hypothesis HC : cs_ok ASEGS ASAN_H BothInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                        (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.
  #[local] Notation g := (hole_granted h).
  #[local] Notation cls := (hole_class h).
  #[local] Notation X := (Xof g E).
  #[local] Notation brk0z := (bv_unsigned brk0).
  #[local] Notation sp0z := (bv_unsigned sp0).
  #[local] Notation argc := (Z.of_nat (length (in_argv inp))).

  #[local] Notation VM := (pm_vmem (bv_unsigned sp0) (bv_unsigned brk0) (Xof g E) FULL).

  Let MC : PMC sp0 rdraw inp brk0z X FULL := PMC_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC.
  Let SOK : pm_syms_ok sp0z brk0z 0 X := pm_syms_ok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC.

  Ltac prepI :=
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP);
    let B := fresh "B" in let Bg := fresh "Bg" in let B13 := fresh "B13" in
    pose proof (KB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as B; cbv zeta in B; destruct B as [B B13];
    unfold pm_kernel_placed in B; rewrite Forall_app in B; destruct B as [B Bg];
    unfold Xof in B, Bg, B13;
    cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted] in B, Bg, B13;
    repeat (apply Forall_cons_iff in B as [? B]); cbn [fst snd] in *;
    pose proof (u64_range brk0) as ?Hb0; pose proof (u64_range sp0) as ?Hs0;
    pose proof (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL) as ?HRIv.
  Ltac zlistsI :=
    unfold pm_vmem in *;
    unfold PM_LAZY, PM_S, PM_ZR, PM_NOACC, PM_MAPS, PM_REM, VISZ, VISZ0, SW;
    rewrite ?(RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl) by assumption;
    unfold Xof in *; cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted map app fst snd] in *.

  #[local] Notation kp_apart := (BsMainIface.kp_apart sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_apart_ne := (BsMainIface.kp_apart_ne sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_facts := (BsMainIface.kp_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_align := (BsMainIface.kp_align sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pd_facts := (BsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b06 := (BsMainIface.kp_b06 h E) (only parsing).
  #[local] Notation kp_b08 := (BsMainIface.kp_b08 h E) (only parsing).
  #[local] Notation kp_b22 := (BsMainIface.kp_b22 h E) (only parsing).
  #[local] Notation vm_full := (BsMainIface.vm_full sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_img := (BsMainIface.vm_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_S := (BsMainIface.vm_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_obj := (BsMainIface.vm_obj sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_ri := (BsMainIface.vm_ri sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_stack := (BsMainIface.vm_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_brk := (BsMainIface.vm_brk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation seg_rom_above := (BsMainIface.seg_rom_above sp0 brk0 inp) (only parsing).
  #[local] Notation seg_rom_below := (BsMainIface.seg_rom_below sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_above := (BsMainIface.mrd_above sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_outside := (BsMainIface.mrd_outside sp0 brk0 inp) (only parsing).
  #[local] Notation vrange := (BsMainIface.vrange sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_sub := (BsMainIface.vr_sub sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_img := (BsMainIface.vr_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_stack := (BsMainIface.vr_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation G_cases := (BsMainIface.G_cases sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zinP_of_In := BsMainIface.zinP_of_In (only parsing).
  #[local] Notation vr_kobj_gen := (BsMainIface.vr_kobj_gen sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b04 := (BsMainIface.kp_b04 h E) (only parsing).
  #[local] Notation kp_b05 := (BsMainIface.kp_b05 h E) (only parsing).
  #[local] Notation kp_b09 := (BsMainIface.kp_b09 h E) (only parsing).
  #[local] Notation kp_b10 := (BsMainIface.kp_b10 h E) (only parsing).
  #[local] Notation kp_b11 := (BsMainIface.kp_b11 h E) (only parsing).
  #[local] Notation kp_b12 := (BsMainIface.kp_b12 h E) (only parsing).
  #[local] Notation kp_b16 := (BsMainIface.kp_b16 h E) (only parsing).
  #[local] Notation kp_b20 := (BsMainIface.kp_b20 h E) (only parsing).
  #[local] Notation kp_b21 := (BsMainIface.kp_b21 h E) (only parsing).
  #[local] Notation kp_b23 := (BsMainIface.kp_b23 h E) (only parsing).
  #[local] Notation vr_b04 := (BsMainIface.vr_b04 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b05 := (BsMainIface.vr_b05 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b09 := (BsMainIface.vr_b09 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b10 := (BsMainIface.vr_b10 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b11 := (BsMainIface.vr_b11 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b12 := (BsMainIface.vr_b12 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b16 := (BsMainIface.vr_b16 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b20 := (BsMainIface.vr_b20 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b21 := (BsMainIface.vr_b21 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b23 := (BsMainIface.vr_b23 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_sw := (BsMainIface.vm_sw sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_b22 := (BsMainIface.vm_b22 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation world_ok_X := (BsMainIface.world_ok_X sp0 h E) (only parsing).
  #[local] Notation bytes_main := (BsMainIface.bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation word_main := (BsMainIface.word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zero_main := (BsMainIface.zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fill_main := (BsMainIface.fill_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation bytes_at_const := (BsMainIface.bytes_at_const sp0 brk0 inp) (only parsing).
  #[local] Notation u8arr_const := (BsMainIface.u8arr_const sp0 brk0 inp) (only parsing).
  #[local] Notation bytes_at_constZ := (BsMainIface.bytes_at_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_img := (BsMainIface.rw_cells_img sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_above := (BsMainIface.rw_cells_above sp0 brk0 inp) (only parsing).
  #[local] Notation cellsZ := BsMainIface.cellsZ (only parsing).
  #[local] Notation cells_wfb := BsMainIface.cells_wfb (only parsing).
  #[local] Notation cells_wfb_sound := BsMainIface.cells_wfb_sound (only parsing).
  #[local] Notation map_b8_unsigned := BsMainIface.map_b8_unsigned (only parsing).
  #[local] Notation map_b8_cellsZ := BsMainIface.map_b8_cellsZ (only parsing).
  #[local] Notation length_cellsZ := BsMainIface.length_cellsZ (only parsing).
  #[local] Notation img_cells_check := BsMainIface.img_cells_check (only parsing).
  #[local] Notation img_cells_main := (BsMainIface.img_cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation lowsh_vm := (BsMainIface.lowsh_vm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation lowsh_vis := (BsMainIface.lowsh_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation u8arr_constZ := (BsMainIface.u8arr_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation fact_ivl := BsMainIface.fact_ivl (only parsing).
  #[local] Notation ivls_of := BsMainIface.ivls_of (only parsing).
  #[local] Notation cover_sweep := BsMainIface.cover_sweep (only parsing).
  #[local] Notation cover_check := BsMainIface.cover_check (only parsing).
  #[local] Notation cover_sweep_sound := (BsMainIface.cover_sweep_sound sp0 brk0 inp) (only parsing).
  #[local] Notation ivls_of_In := BsMainIface.ivls_of_In (only parsing).
  #[local] Notation Mr_some' := (BsMainIface.Mr_some' sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_nonnull := (BsMainIface.Mr_nonnull sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation uE_lit' := (BsMainIface.uE_lit' E) (only parsing).
  #[local] Notation estart_lit := (BsMainIface.estart_lit sp0 brk0 inp E) (only parsing).
  #[local] Notation fact_ivl_sound := (BsMainIface.fact_ivl_sound sp0 brk0 rdraw inp ch E R FULL model HC) (only parsing).
  #[local] Notation cover_main := (BsMainIface.cover_main sp0 brk0 rdraw inp h ch E R FULL model Hh HC) (only parsing).
  #[local] Notation lowsh_stk := (BsMainIface.lowsh_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_word_main := (BsMainIface.img_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zscanN := BsMainIface.zscanN (only parsing).
  #[local] Notation zscanN_sound := (BsMainIface.zscanN_sound sp0 brk0 inp) (only parsing).
  #[local] Notation segment_byte_at_zero1 := (BsMainIface.segment_byte_at_zero1 sp0 brk0 inp) (only parsing).
  #[local] Notation obj_word_main := (BsMainIface.obj_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_bytes_main := (BsMainIface.obj_bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_zero_main := (BsMainIface.obj_zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation world_uw := (BsMainIface.world_uw sp0 h) (only parsing).
  #[local] Notation rw_cells_cons1 := BsMainIface.rw_cells_cons1 (only parsing).

  #[local] Notation all_holes_w_here := (BsMainCells.all_holes_w_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation all_holes_here := (BsMainCells.all_holes_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation hole_sel_here := (BsMainCells.hole_sel_here sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hole_short_pm := (BsMainCells.hole_short_pm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation csym_den := (BsMainCells.csym_den sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation uE_lit := (BsMainCells.uE_lit E) (only parsing).
  #[local] Notation zero_sound := (BsMainCells.zero_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation fill_sound := (BsMainCells.fill_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation bytes_sound := (BsMainCells.bytes_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation word_sound := (BsMainCells.word_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_sound := (BsMainCells.img_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vav Hh HC) (only parsing).
  #[local] Notation argH0_low := (BsMainCells.argH0_low sp0 brk0 rdraw inp E Vsp Vav) (only parsing).
  #[local] Notation hid_img := (BsMainCells.hid_img sp0 brk0 rdraw inp ch E model Vsp Vav) (only parsing).
  #[local] Notation brk_facts := (BsMainCells.brk_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VISK_bound := (BsMainCells.VISK_bound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VM_Z := (BsMainCells.VM_Z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_vis := (BsMainCells.hid_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_sh := (BsMainCells.hid_sh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_stack := (BsMainCells.hid_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation visibleZ_hid := (BsMainCells.visibleZ_hid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation args_block := (BsMainCells.args_block sp0 brk0 rdraw inp ch E R FULL model Vsp Vav Vev Vfit HC) (only parsing).
  #[local] Notation Mr_some := (BsMainCells.Mr_some sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_vis_none := (BsMainCells.Mr_vis_none sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation rdn_Mr_full := (BsMainCells.rdn_Mr_full sp0 brk0 rdraw inp ch E FULL model) (only parsing).

  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  Lemma ahm_tb : rw_cells asegs VM 0x190888 [C8 (wz (ps_b05 X))].
Proof.
ltac2:(KReplay.run1 (kr_t_BsMainIfaceAHM ()) ["AT_MAIN"] "p'0h07__arithh14__ffh28__varmaph35__with44__x1h51Hh61zi001sp;1p;2p;3p;4p;Fp;6p;7g0000j1=Tg000Pj1jTg0010j2JTg001Nj1BTg001lj1iTg002Wj2[Tg003:j25Tg003]j3;Tg004@j48Tg004kj2ATg005Mj2@Tg005gj2?Tg006Sj37Tg006mj3fTg007Lj4\Tg008>j29Tg008[j1YTg009bj2XTg00:`j1WTg00;`j4UTg00<@j3TTg00<]j1ITg00=]j1HTg00>]j1ETg00?]j1DTg00@]j1FTg00A]j1GTg00B]j1CTg00C]j1KTg00D]j1LTg00E]j1MTg00F]j1NTg00G]j1OTg00H]j1PTg00I]j1QTg00J^j1RTg00Kfj10Tg00LKj1STg00Lij2>Tg00MSj1hTg00NYj1gTg00OXj3eTg00P5j4bTg00Q6j4]Tg00R8j11Tg00R]j16Tg00S;j1ZTg00T2j1^Tg00Toj3_Tg00UOj4`Tg00VMj1aTg00Vkj2<Tg00WGlFcTg00XOj6dTg00Xkj7VTf1R0g00YOg00YnR1P1g00ZNR1f0R2g00ZnFVp=:%02#0p=2%02#0#0#0p=4%12#0p=3g00[NR3g00[lR4#=R5%j4R41J30%B3R6%i3R7P3g00\XR8,[3R9g00]=R:,535;3g00][P9C8':1A71R1P2f2R9g00^BR;g00^bR<'@R=1?29=7;<dAf3:0C\R0b1b2b3W4192:=732^43P2p,1hR<#Yp,1ER;'XR9#WR>O1b0g00_BR?P3P?P3g00`CP:CUR@9T?3P:%I9P>%H9%E9%D9%F9%G9%C9%K9%L9R:%M9%N9%O9%P9%Q9%R9%08#2RA#0#2#SRBp,3sp0RC'>RD%hDp,4brk0RE,>BRB%g:n01100000E000000000000000000000000000000000000000000Ae?3@'9=73>ePDPBP9P@CbR?=73>R:eP:P3P?g00aDPDPBP9p,4FULLR9C]%18#2#1#4#3#2#3#2#3#2#6RBg00b;RD%Z2#^%=D3_C`X63PCPEp,5rdrawp,3inpP<p,2chP;p,1RP9p,5modelp,3Vspp,4Vbrkp,3Vavp,3Vevp,4Vfitp,2Hhp,2HCPBP@P=P5P4%a3R=P6P3%08#1#1#1#1#1#3#4#4#4#6R@,53g00c8R9153BR;C8,:7P1P0b1b2b31<@BP2b0P5P4P=P6P3%6ARA,539;3;P9%38#1#1#3#3#2#4#4#4#6R8,53C8,:7P1P0b1b2b319BA/<8P2b0MFcP>P2Edb5o"). Qed.

  Lemma ahm_geom : 4096 <= ps_b05 X /\ ps_b05 X mod 4096 = 0 /\ ps_b05 X + 0x38e000 <= page_down sp0z - 8388608
                   /\ (ps_b05 X + 0x38e000 <= 65536 \/ 7241728 <= ps_b05 X) /\ (ps_b05 X + 0x38e000 <= 2147446784 \/ 17594333495296 <= ps_b05 X).
Proof.
ltac2:(KReplay.run1 (kr_t_BsMainIfaceAHM ()) ["AT_MAIN"] "h01Hh12H0h24__x1h34__x2h44__x3h51Ah61Bh71Ch81Dh91Fh:2H1h;2H2h<2H3h=2H4h>7__arithh?4__ffh@6__sat1hA8__varmaphB5__witp;1p;2p;4p;Cp;3p;7p;8g00c_j1sTg008[j1rTg009bj2\Tg00:`j1PTg00R8j13Tg00Kfj10Tg00R]j17Tg00;`j4MTg00d>j2LTg00e?lCqTg00<@j3lTg00fBj2GTg00Vkj21Tg00OXj3aTg008>j28Tg00LKj1^Tg00Lij2]Tg00fbj1[Tg00gej2CTg00hBR0j22Tg00h]j2YTg00iNj2XTg00ioj1WTg00jHj2VTg00jej2OTg006Sj3?Tg00kBj2NTg00kij2>Tg00lEj2QTg00llj2RTg00mRj2STg00n8j2TTg00o<j2UTg005Mj2KTg0000j1pTg000Pj1oTg0010j2HTg00o]j4kTg001Nj1gTg001lj1fTg003:j2FTg002Wj2DTg010;j1cTg003]j3bTg010]j3dTg004@j4ETg004kj2`Tg005gj2_Tg006mj3hTg007Lj4iTg011@j2jTg00Xkj7JTg011Zj8mTg012>j7nTg012bj7ZTf0R1#0#0p=<%31#3p=B%01#0#0#0p=9%01#0#0#0#0#0#0#0p=Ag00[NR2g00]=R37?1p==f3R4f2R5'1f1R6/11'jp=6%31#3#3#3p=;P5g00YOR7g00YnR8P8g00ZNR9P2P6g00c8P1CEg00ZnR:FJp=41F21p=:P4P7P8P8P9P5P6P1Gmp=5P5P7P8P8P9P6P1Fnp=IP6P7P8P8P9P1P:FJp=eP5P7P8P8P9P6P1FZp=@p,3sp0R7p,4brk0p,5rdrawp,3inpp,1hR:p,2chp,1ER;p,1Rp,4FULLp,5modelp,3Vspp,4Vbrkp,3Vavp,3Vevp,2Hhp,2HCg013F#sP2P2%r:/\;#PR<g00\XR=#3R>#3R?#0#<#3#B#0#9#A#7R@CMRA1L:;MCqAl22AR;%0=R:#0#9RB#<#9RC#7RD'G#=RE11D;RFAa22A,8;RA%^B/]7#[R7%0CRC#0#<RB#0#<#9#7RG'CRH'1RIPA%7BRB%3=#0#3#B#0#3#0#<#9#A#7RJP;C6RKPA%;?#;#;#0#3#B#9#A#7R?%;C#;#;#;#0#<#9#A#7RCP;C6R;'2RA'2RL'2RM'2P0PEPM11D<1G<DRN#=18<@RO/1HPOPBPJP<C6POP?PCP<C6'2'2'2'2ROP1P0PFPLPOP1P0PIPAPOP1P0PKP;POP11Y<D113<113DR0113NRH[[1X<D%=DRP#W1V<DRQ,OD/8N9?2<[1N<D1>3DRR1>ND,2HRH[1Q<D1>D31>DN11N3'2[1R<D%=Q\P1S<DA?2N<\Pg013e1T<DRPePPf4RPg014A1U3D'KPReO1PHg00[lRH#p%oHP21H25P61H24Ck%g2%f2RHPH1F23RR1D2=R=54H%c8R8PH%:DRQ94HRP81D2:R:94HRC5C5P8PH%:@9b2=RS%:?54H%:C=4H=5IHRTP8PH%:B94HS%:J=4H=5IHRUP8PH1D2>%:G5d294HSRSP8PHA4HQ=RQP8PHP2P:g00][PRCE,eHRRP8A@HUT9@HS9@HR9@HQC5C5C5C5C5C51`H9P1P5g00^BRHg00^bR9'K1_15=?H9dAh236Cib?bAbBX22X32X4211311134\0[186@P?PCP6C6185@PBPJP5C6184@f5/CG'111DPf6RP#=11DPf7#=18P@R@f8RD/CG'1P@PBPJPPC6P@P?PCPPC6'2'2'2'2[[[[[[^22^32^42P1P7PNP<PDf9f:f>fBfFO9b>b1POeb=b<b;b:b1b0b@X9;X8KP6P1O2n2011000010121000000X0AX7IP6P1O2n2011000010121000000X0LX6FP6P1O2n2011000010121000000X0MX5EP6P1O2n2011000010121000000b0o"). Qed.

  Lemma ahm_zero : forall z, ps_b05 X <= z < ps_b05 X + 0x38e000 -> VM (wa z) = Some (b8 0).
Proof.
ltac2:(KReplay.run1 (kr_t_BsMainIfaceAHM ()) ["AT_MAIN"] "p'0h07__arithh14__ffh28__varmaph35__with41Hh52Hyh62H0h72Hzh84__x1h94__x2h:2H1h;2H2h<2H3h=2H4h>2Hah?6__sat1h@6__sat4hA1yhB2G1hC2G2hD2G3hE2_HhF6__sat0hG1xhH1zi001sp&0p;1p;2p;5p;3p;4p;Hp;Jp;7p;<p;6p;8g008[k10OTg009bk20NTg00:`j1~Tg00R8j13Tg00Kfj10Tg00R]j14Tg008>j22Tg00Vkj27Tg00fBk20MTg00LKj1^Tg00Lij2[Tg00fbk10;Tg00gek205Tg011@j2XTg00hBR0j2;Tg014gj1}Tg015Jj1xTg015lj1JTg00Q6j5LTg016cj1oTg017Zj2nTg006Sj36j1WTg00;`j4STg005Mj2:Tg018<j1iTg019>j2fTg01:Ej2eTg00kij2>Tg01:mj2aTg01;Jj3`Tg00o<j2RTg0000j1_Tg000Pk10LTg00VMk10KTg001Nk10FTg001lk10ETg003:j2BTg01;nk30DTg004kk20=Tg006mk30<Tg007Lj4YTg00P5k40:Tg00c_j15Tg00d>k204Tg00ioj1<Tg01<QR1j1UTg01=1k202Tg01=Tk301Tg01>1j3NTg005gj2|Tg01>Zj4MTg00h]j2{Tg00iNj2wTg00jHj2tTg00jej2sTg00kBj2rTg00lEj2uTg00llj2vTg00mRj2qTg00n8j2pTg0010j2yTg00o]j4zTg002Wj2\Tg003]j3ITg010;k100Tg00<@j3ZTg00<]j1mTg00=]j1lTg00>]k103Tg00?]j1kTg00@]k106Tg00A]k107Tg00B]j1jTg00C]k108Tg00D]k109Tg00E]j1hTg00F]j1gTg00G]k10>Tg00H]k10?Tg00I]k10@Tg00J^k10ATg00MSk10BTg00NYk10CTg00OXj3]Tg01?ElHdTg01@FlJcTg004@j4QTg00Xkj7bTg012bk70GTg01AJm<0HTg01Aok60ITg011Zk80JTf0R2#0#0p=9%32#3p=D%02#0#0#0p=A%02#0#0#0#0#0#0#0p=Cf3R3f2R4'7f1R5/>2';p=1g00[NR6g00]=R7762p=P%32#3#3#3p==1772p=?P6P5g00c8P2CQp=OP5g00YOR8g00YnR9P9g00ZNR:P2g00ZnFbp=8P6P5g01BSP2CQp=EP4P8P9P9P:P5P2K0Gp=K1>52,;4p=TA6652p=@g01C:R;P6P2P1P5P4P3f4R1f5f6f7R<f8N<0Hp=FP6P5g00][P2CQp=HP5P8P9P9P:P2J0Ip=GP3P8P9P9P:P4P5P2L0Jp=Vp,1hR8$0OR=p,1ER>+0NR?#~R@P2P2g00\XRA#3RB#3RC#0#9#3#D#0#A#C#4RD,2@REC1g01CY%0ARF#9RG#0#9RH#9#ARI#4RJ/7@RK20M@JRL#PRM%^HRNp,3sp0RO'[RP$0;%0IRI#0#9RQ#0#9#A#4+05,7ERR%4Q,7E%3A#0#3#D#0#3#0#9#A#C#4/7@'X%=C#=#=#0#3#D#A#C#4,7E%=I#=#=#=#0#9#A#C#4/7@'X';RI';RC';RQ';P0PKPQ%^G#}RG#xRSPPp,4brk0RT,[NRUP?p,4FULLRV%J3DL%o7,nGRG36P2P0PMPCPPPUP?PV%J<DL=6SGP2P0PRPIPPPUP?PVf;R0#JDL=6SGP2POPTp,5rdrawRGp,3inpRSP8p,2chR<P>p,1RR3PVp,5modelRWp,3VspRXp,4VbrkRYp,3VavRZp,3VevR[p,4Vfitp,2HhR\p,2HCR]g01D_g00_BR^P6g00`CP7CSR_PDg00^BR`g00^bRa':Rb%iP/f=%4FR=%4HRH'e1>7=%?H1a=HRc,>7[Rd[%?=Reg01E_RfA`=H5UW>%?c\f^>eP5g014ARe1R7=':O1Pdg00[lRd#_Rf&0LdRd&0K6RH&0F6Rg&0E6Rh1B67Ri1B6DRj'O,8h1B6=Rk>0D6N,Ej,8h3K20=h:R:P2P4PbB0<675RNCYb1b2b3%?D?TDcP2b0b?bFb?PPPUP?P_H0:RcP2P212cDRlC1POPTPGPSP8P<P>P3PVPWPXPYPZP[P\P]g013F#5R]P6P6P@PDCSR\P52048>%5]R>96;]R8#<%4AR[/@=RZ#<%W;RY%W6RX%U5%U2'@A6;5220252401XA;XG;RWP]P[1:6[RVP>P=1:6=M9F9N8ZPfPdPHPg1B6[R8/Hk,8h,GhP:P2P4Pb1|24=6`adPNCYRNb1b2b3g01F;Ra\ZP2b0CM%5>R>96;]RZ#<%4BRB,@[R`#<PYPXPWP]P[PVP>PB1:6BM9F9NZ`PfPdPHPg1B6B,H8,8h,GhP:PNb1b2b3Pa\`P2b0CM%5>#5#5#5#5#5#5#5R>96;]R;#<%DF#4R`,@[RB#<PYPXPWP]P[PVP>P`1:6`M9F9N;BPfPdPHPg1B6`,H8,8h,GhP:PNb1b2b3Pa\BP2b0CM12@7RBP5P512BDRaC1R81{@JR`%?@%?J%?LR;[[R>1w@JRV%PJR[#<1t@JR],sJ/2L,@@[RW1r@JRX1>7JRYAT;LJR;[RZ1u@JRb1>J71>JL17L7';[Rk1v@JR=%P]\[R]1q@JR31@L@\[R[g013e1p@JRLeR<PLP11R7J,:ePYeO1RYP;PfPdP61y64P5PHCzRHPgPh1\6ARA=I6iRi1\6FRF'O,8hAI6ij,EF,8h5KhRi&009R91OAF,8hAI6Aj,EF,8h5KhRFCVP:PNb1b2b3X86X961227RAP5P512ADC1P5P4P4125DC1[^86^96P2P0P@f9R0O3b0b6P@P0P0PEC1eb=b<b;b:b6b4b@W5P@P4P4PEC1^58eP^P6AZ^6_P7%m?P@%l?&03?%k?&06?&07?%j?&08?&09?R8%h?%g?&0>?&0??&0@?&0A?PP&0BPPU&0C8n01100000E000000000000000000000000000000000000000000A]^6_'2R_P5P512_DR^C1AZ66\R8P4P4A]66\,28C1R8]5ePcP5P5PlC1P8]5eP2O1MHdW5XA6f>R8P@P8P8PEC1REP`P>PVPWPXPZPbPkP=P]P3P[P<PLPYP;PfPdPHPgPhPFP9PiCVP:PNb1b2b3X86X96P2P5P5122DC11257R7P4P4127DC1[^86^96P2fHP@P0O3b0b6PBfFRBPBPaC1eb=b<b;b:b6b4b@W7P_f?R_P_P^C1^7EePcP_P_PlC1^7Eef=O1MJcXEIXDRP5P2O2n2011000000121000000X4CXCMP5P2O2n2011000000121000000X4QXBKP5P2O2n2011000000121000000b4W7XH6o"). Qed.

  Lemma ahm_stk : stk asegs VM (ps_b05 X) (ps_b05 X + 0x38e000).
Proof.
ltac2:(KReplay.run1 (kr_t_BsMainIfaceAHM ()) ["AT_MAIN"] "h01Hh12H0h22H6h34__x1h46__sat4h56__sat5h64__x2h72H1h83H10h92H2h:2H3h;2H4h<2H5h=2H7h>2H8h?2H9h@2HahA7__arithhB4__ffhC8__varmaphD5__withE1ahF4__p1hG4__p2hH4__x3hI4__x4hJ2G1hK2G2hL2G3hM2PDhN2_HhO6__sat6hP6__sat7hQ1bhR2zhp%0p&0p;1p;2p;4p;@p;3p;6p;5p;7p;8g00Kfj10Tg00R]j15Tg008[k10<Tg009bj2zTg00:`j1oTg00Vkj21Tg00fBj2[Tg00R8j13Tg008>j29Tg00LKj1`Tg00Lij2]Tg00fbk108Tg00gej2ZTg011@j2YTg00hBR0j22Tg00Q6j4nk501Tg01FXj4lTg01GSl@kTg00kij24Tg00h]j2UTg00iNj2TTg00ioj1eTg00jHj2\Tg00jej2HTg006Sj3:Tg00kBj2PTg00lEj2OTg00llj2QTg00mRj2RTg00n8j2NTg00o<j2STg005Mj2JTg0000k10@Tg000Pk10?Tg0010j2MTg001Nk10>Tg001lk10=Tg002Wj2ETg010;k10;Tg003:j2_Tg004kk207Tg005gk203Tg006mk302Tg007Lj4~Tg01:Ej2}Tg01:mj2{Tg01;Jj3yTg00c_j1BTg01HVj2XTg01I?j2xTg01Ihj3uTg01JQj1tTg01Joj2sTg01KPj3WTg01L9j2mTg01Lej2pTg00Toj3qTg00VMj1rTg00o]j4LTg01Aoj6vTg01MQj3wTg003]j3VTg010]j3jTg01;nj3iTg014gj1|Tg015Jj1hTg015lk100Tg017Zj2gTg016cj1fTg004@j4GTg01N4k204Tg01O:k405Tg01OTk606Tg00Xkj7dTg011Zk809Tg01PZk30:Tg01QCj6cTg012bj7bTf0R1#0#0p=a%01#0#0p=<%01#0#0#0p=?g00[NR2g00]=R37:1p=C%31#3p=I%01#0#0#0#0#0#0#0p=7%31#3#3#3p==1131p=81_21p=DP2f1R4g00c8P1CGp=>P4g00YOR5g00YnR6P6g00ZNR7P1g00ZnFdp=6f3R8P5P6P6P7f2R9P4P1L09p=;1X21p=@B0:241p=AP2P4g00][P1CGp=KP4P5P6P6P7P1Ecp=^P9P5P6P6P7P4P1Fbp=Fg01CYg00\XR:#0R;#aS00#<R<#a#?R=#5R>p,1hR?$0<p,1ER@'zS01#oRA'1RB1[A>RC#CRD%3:S02#3RE#<#3#I#0#?#7#5RF,9ARG%`<RHp,3sp0RI']RJ$08RK%0=R=#<RL#<#?RM#5RN'Z'1RO%5L,1G%3:#0#3#I#0#3#<#?#7#5/1A'Y%=E#=#=RL#0#3#I#?#7#5,1G%==#=#=#=#<#?#7#5/1A'Y'2R='2RP'2RQ'2P0PBPQg00aDPJp,4brk0RR,]HS03Q01p,4FULLS04CnRSPAPGClRTP1P0PDPPPTP1P0POP=PTP1PIPRp,5rdrawp,3inpP?p,2chP@p,1RQ04p,5modelp,3Vspp,4Vbrkp,3Vavp,3Vevp,2Hhp,2HCM@k11KJ19K>,4J'2S05%3L#<#?#7#7#7#5RL/1K%7M#7#7#5RM,1K'21[K>R@#CS06'2'2PSPAPG1UA>S07%8ARS%8>R?%8CRR[[S081UK>S09%8K%8@RI\?[S0:1TK>S0;%C>R?#eRT1\K>R0,H>/9@9:2K[RU1PK>RV143>RW14@>,2IRI[RX1OK>RY14>3RZ14>@11@3'2[R[1QK>R\%C0\?R01RK>R]A:2@K\?R@g013eR^1NK>R_eR`P_1TA>Ra1\A>Rb,H>/9C9:2A\TRT1PA>Rc14C>,2RRR\WRd1OA>Re14>C11C3'2\ZRZ1QA>Rf%Cb\?Rg1RA>RhA:2CA\?RiP^1NA>R^eRjP^f4Rkg014ARl1S3>'JPWeRWO1RmPRf;S0<PWO1RWPIg00[lRn$0@Ro&0?nRp1M24&0>2Rq&0=2Rr%D>Rs1E2:Rt'>,6r&0;6Ru1_23Rv/>t,6rC;207r7RwP1P9g00^BRxg00^bRy'J20319=:xydB02234C~RybBbCbDX3211>1%84[^32P1PAfKO2bAb1b2PSeb8b?b>b=b2b<b;b:b9b7b1b0b4b5Q07Q08Q09Q0:%5;RS%5<R<'}143SRx%8<1{S<Rz,43[R{[%8SR|g01E_R}AyS<4UW@%8zR<\}^@|Q0;PUPVPXPYP[P\P0P]P@P`P_PaPTPcPdPePZPfPgPhPiPjP^PmPRPWPIP9P}f@P1P4O2XE|P<^E|fAS0=1S3S,JlPxeO1P{p-0R{g013FRx#BRl#BR|#BR<#BR}#BR~#@%@l1X2xRx'A'A1x2>=u2x%t:,s2R:%B~#@5W2%@}%@<%@|9W2:'A'A'A'Ag01Qg'm'p=qnoPpP21M29RnP4P2%r2R:P81M2kCLCLPqPrPrPrP5P6P6P71Ksv,6rEvPu1E2E9w2s1E2;R;5V2,Kt,6rC;PuPrf6Rs,^r%DLQ02,E2RE'>,6r%DM,>E,6r5Frf7,^r5Fr5FrPuPr%DF9V2tR7%DN9j2E'>,6rPuPr1K;v,6rPu%DS=i2H,>7,6rC;C;C;C;PwPybBbCbDX32X62XH2XI2XF{WGg01F;\?1H>k/999:24[f511L8118M'2/2s'2199F1ZkN'1%Ck19kF/1z[[[[^32^62^H2^I2^F{^G{P1Q06Q05PbPKPCPAQ0<fFfHfLO:bAb5b4bRb1b211Gzeb8b?b>b=b2b<b;b:b9b7b1b0b4b5bObP11A1141G'2Q00#`#|Rz%hzPJQ03Q01Q04&009I011gz13:XQz%f3Q07Q08Q09Q0:Q0;PUPVPXPYP[P\P0P]P@P`P_PaPTPcPdPePZPfPgPhPiPjP^PmPRPWPIPoPpP2PnP4P:CLPqPr1>t;,6rP2P;g01BSP7CG,6r5FrRrPuPrC;PwPybBbCbDX32X621114191F,44'21149194F,49'2[^32^62P1fBPAQ0=O3bAb1b2f?R9,1A149G'2eb8b?b>b=b2b<b;b:b9b7b1b0b4b5-044H05W@XE2J06bMXN=XLOP4P1O2n2011000000121000000X0PXKDP4P1O2n2011000000121000000X0QXJBP4P1O2n2011000000121000000b0o"). Qed.
End AT_MAIN.
