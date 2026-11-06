(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HStep HLFrame HArr CellsX TacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsStack0.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsImages AsPlanImages AsHSTab AsStartupHSF AsMainVM AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface LazyRestrict LazySR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsMainSyms.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_AsMainIfaceAHM () := "K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib3bpA5Start;AsMainFacts<hole_grantedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsMainFacts3XofC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b05C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b04C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b06C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b08C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b09C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b10C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b11C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b12C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b13C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b16C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b20C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b21C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b22C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms6ps_b23C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms7ps_b19rC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms>pm_region_infoC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib3bpA5Start:AsMainSyms<pm_stack_topC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start:AsMainSyms5pm_shC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC69OSSVerify5KrLib3bpA5Start;AsMainCells6cx_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsMainIface7pm_vmemC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C79OSSVerify5KrLib3bpA2HF3Lib4TacX2wzC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell01C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C79OSSVerify5KrLib3bpA2HF3Lib5HStep8rw_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib3bpA5Start;AsMainIface=img_word_mainC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I69OSSVerify5KrLib3bpA5Start;AsMainCells4csym00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpA5Start;AsMainCells4csym03C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt5ASegs5asegsC1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib3bpA2HF3Lib6HCells4cell00C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat02C69OSSVerify5KrLib3bpA5Start;AsMainIface6kp_b05C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsMainIface8kp_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC69OSSVerify5KrLib3bpA5Start:AsMainSyms9page_downC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC79OSSVerify5KrLib3bpA2HF3Lib:HLiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr04I47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes3nat01K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib3bpA2HF3Lib4HMem2waC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib3bpA2HF3Lib4TacX2b8C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib3bpA5Start:AsMainSyms8pm_shortC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsMainCells<world_ok_allC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses9not_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib3bpA5Start;AsMainIface6vm_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsMainIface9zero_mainC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes3nat00c69OSSVerify5KrLib3bpA5Start>AsMainIfaceAHM8ahm_geomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsMainCells5w_allC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00C79OSSVerify5KrLib3bpA2HF3Lib7HLFrame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA5Start;AsMainIface8pd_factsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega7EnvRing5PExpr05c69OSSVerify5KrLib3bpA5Start>AsMainIfaceAHM8ahm_zeroC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib3bpA5Start;AsMainIface;stk_of_someC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega:ZMicromega;ZArithProof01".
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
  Hypothesis HC : cs_ok ASEGS ASAN_H AsanInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
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

  #[local] Notation kp_apart := (AsMainIface.kp_apart sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_apart_ne := (AsMainIface.kp_apart_ne sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_facts := (AsMainIface.kp_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_align := (AsMainIface.kp_align sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pd_facts := (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b06 := (AsMainIface.kp_b06 h E) (only parsing).
  #[local] Notation kp_b08 := (AsMainIface.kp_b08 h E) (only parsing).
  #[local] Notation kp_b22 := (AsMainIface.kp_b22 h E) (only parsing).
  #[local] Notation vm_full := (AsMainIface.vm_full sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_img := (AsMainIface.vm_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_S := (AsMainIface.vm_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_obj := (AsMainIface.vm_obj sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_ri := (AsMainIface.vm_ri sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_stack := (AsMainIface.vm_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_brk := (AsMainIface.vm_brk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation seg_rom_above := (AsMainIface.seg_rom_above sp0 brk0 inp) (only parsing).
  #[local] Notation seg_rom_below := (AsMainIface.seg_rom_below sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_above := (AsMainIface.mrd_above sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_outside := (AsMainIface.mrd_outside sp0 brk0 inp) (only parsing).
  #[local] Notation vrange := (AsMainIface.vrange sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_sub := (AsMainIface.vr_sub sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_img := (AsMainIface.vr_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_stack := (AsMainIface.vr_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation G_cases := (AsMainIface.G_cases sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zinP_of_In := AsMainIface.zinP_of_In (only parsing).
  #[local] Notation vr_kobj_gen := (AsMainIface.vr_kobj_gen sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b04 := (AsMainIface.kp_b04 h E) (only parsing).
  #[local] Notation kp_b05 := (AsMainIface.kp_b05 h E) (only parsing).
  #[local] Notation kp_b09 := (AsMainIface.kp_b09 h E) (only parsing).
  #[local] Notation kp_b10 := (AsMainIface.kp_b10 h E) (only parsing).
  #[local] Notation kp_b11 := (AsMainIface.kp_b11 h E) (only parsing).
  #[local] Notation kp_b12 := (AsMainIface.kp_b12 h E) (only parsing).
  #[local] Notation kp_b16 := (AsMainIface.kp_b16 h E) (only parsing).
  #[local] Notation kp_b20 := (AsMainIface.kp_b20 h E) (only parsing).
  #[local] Notation kp_b21 := (AsMainIface.kp_b21 h E) (only parsing).
  #[local] Notation kp_b23 := (AsMainIface.kp_b23 h E) (only parsing).
  #[local] Notation vr_b04 := (AsMainIface.vr_b04 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b05 := (AsMainIface.vr_b05 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b09 := (AsMainIface.vr_b09 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b10 := (AsMainIface.vr_b10 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b11 := (AsMainIface.vr_b11 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b12 := (AsMainIface.vr_b12 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b16 := (AsMainIface.vr_b16 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b20 := (AsMainIface.vr_b20 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b21 := (AsMainIface.vr_b21 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b23 := (AsMainIface.vr_b23 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_sw := (AsMainIface.vm_sw sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_b22 := (AsMainIface.vm_b22 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation world_ok_X := (AsMainIface.world_ok_X sp0 h E) (only parsing).
  #[local] Notation bytes_main := (AsMainIface.bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation word_main := (AsMainIface.word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zero_main := (AsMainIface.zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fill_main := (AsMainIface.fill_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation bytes_at_const := (AsMainIface.bytes_at_const sp0 brk0 inp) (only parsing).
  #[local] Notation u8arr_const := (AsMainIface.u8arr_const sp0 brk0 inp) (only parsing).
  #[local] Notation bytes_at_constZ := (AsMainIface.bytes_at_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_img := (AsMainIface.rw_cells_img sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_above := (AsMainIface.rw_cells_above sp0 brk0 inp) (only parsing).
  #[local] Notation cellsZ := AsMainIface.cellsZ (only parsing).
  #[local] Notation cells_wfb := AsMainIface.cells_wfb (only parsing).
  #[local] Notation cells_wfb_sound := AsMainIface.cells_wfb_sound (only parsing).
  #[local] Notation map_b8_unsigned := AsMainIface.map_b8_unsigned (only parsing).
  #[local] Notation map_b8_cellsZ := AsMainIface.map_b8_cellsZ (only parsing).
  #[local] Notation length_cellsZ := AsMainIface.length_cellsZ (only parsing).
  #[local] Notation img_cells_check := AsMainIface.img_cells_check (only parsing).
  #[local] Notation img_cells_main := (AsMainIface.img_cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation lowsh_vm := (AsMainIface.lowsh_vm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation lowsh_vis := (AsMainIface.lowsh_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation u8arr_constZ := (AsMainIface.u8arr_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation fact_ivl := AsMainIface.fact_ivl (only parsing).
  #[local] Notation ivls_of := AsMainIface.ivls_of (only parsing).
  #[local] Notation cover_sweep := AsMainIface.cover_sweep (only parsing).
  #[local] Notation cover_check := AsMainIface.cover_check (only parsing).
  #[local] Notation cover_sweep_sound := (AsMainIface.cover_sweep_sound sp0 brk0 inp) (only parsing).
  #[local] Notation ivls_of_In := AsMainIface.ivls_of_In (only parsing).
  #[local] Notation Mr_some' := (AsMainIface.Mr_some' sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_nonnull := (AsMainIface.Mr_nonnull sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation uE_lit' := (AsMainIface.uE_lit' E) (only parsing).
  #[local] Notation estart_lit := (AsMainIface.estart_lit sp0 brk0 inp E) (only parsing).
  #[local] Notation fact_ivl_sound := (AsMainIface.fact_ivl_sound sp0 brk0 rdraw inp ch E R FULL model HC) (only parsing).
  #[local] Notation cover_main := (AsMainIface.cover_main sp0 brk0 rdraw inp h ch E R FULL model Hh HC) (only parsing).
  #[local] Notation lowsh_stk := (AsMainIface.lowsh_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_word_main := (AsMainIface.img_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zscanN := AsMainIface.zscanN (only parsing).
  #[local] Notation zscanN_sound := (AsMainIface.zscanN_sound sp0 brk0 inp) (only parsing).
  #[local] Notation segment_byte_at_zero1 := (AsMainIface.segment_byte_at_zero1 sp0 brk0 inp) (only parsing).
  #[local] Notation obj_word_main := (AsMainIface.obj_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_bytes_main := (AsMainIface.obj_bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_zero_main := (AsMainIface.obj_zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation world_uw := (AsMainIface.world_uw sp0 h) (only parsing).
  #[local] Notation rw_cells_cons1 := AsMainIface.rw_cells_cons1 (only parsing).

  #[local] Notation all_holes_w_here := (AsMainCells.all_holes_w_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation all_holes_here := (AsMainCells.all_holes_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation hole_sel_here := (AsMainCells.hole_sel_here sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hole_short_pm := (AsMainCells.hole_short_pm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation csym_den := (AsMainCells.csym_den sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation uE_lit := (AsMainCells.uE_lit E) (only parsing).
  #[local] Notation zero_sound := (AsMainCells.zero_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation fill_sound := (AsMainCells.fill_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation bytes_sound := (AsMainCells.bytes_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation word_sound := (AsMainCells.word_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_sound := (AsMainCells.img_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vav Hh HC) (only parsing).
  #[local] Notation argH0_low := (AsMainCells.argH0_low sp0 brk0 rdraw inp E Vsp Vav) (only parsing).
  #[local] Notation hid_img := (AsMainCells.hid_img sp0 brk0 rdraw inp ch E model Vsp Vav) (only parsing).
  #[local] Notation brk_facts := (AsMainCells.brk_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VISK_bound := (AsMainCells.VISK_bound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VM_Z := (AsMainCells.VM_Z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_vis := (AsMainCells.hid_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_sh := (AsMainCells.hid_sh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_stack := (AsMainCells.hid_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation visibleZ_hid := (AsMainCells.visibleZ_hid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation args_block := (AsMainCells.args_block sp0 brk0 rdraw inp ch E R FULL model Vsp Vav Vev Vfit HC) (only parsing).
  #[local] Notation Mr_some := (AsMainCells.Mr_some sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_vis_none := (AsMainCells.Mr_vis_none sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation rdn_Mr_full := (AsMainCells.rdn_Mr_full sp0 brk0 rdraw inp ch E FULL model) (only parsing).

  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  Lemma ahm_tb : rw_cells asegs VM 0x18ef48 [C8 (wz (ps_b05 X))].
Proof.
ltac2:(KReplay.run1 (kr_t_AsMainIfaceAHM ()) ["AT_MAIN"] "p'0h07__arithh14__ffh28__varmaph35__with44__x1h51Hh61zi001sp;1p;2p;3p;4p;Fp;6p;7g0000j1>Tg000Pj1kTg0010j2STg001Nj1CTg001lj1jTg002Wj2\Tg003:j25Tg003]j3<Tg004@j49Tg004kj2BTg005Mj2ATg005gj2@Tg006Sj38Tg006mj3fTg007Lj4]Tg008>j2;Tg008[j1ZTg009bj2YTg00:`j1XTg00;`j4VTg00<@j3UTg00<]j1RTg00=]j1QTg00>]j1HTg00?]j1ETg00@]j1FTg00A]j1GTg00B]j1DTg00C]j1ITg00D]j1JTg00E]j1KTg00F]j1LTg00G]j1MTg00H]j1NTg00I]j1OTg00J^j1PTg00Kfj10Tg00LKj1TTg00Lij2?Tg00MSj1iTg00NYj1hTg00OXj3eTg00P5j4cTg00Q6j4bTg00R8j11Tg00R]j17Tg00S;j1[Tg00T2j1^Tg00Toj3_Tg00UOj4`Tg00VMj1aTg00Vkj2=Tg00WGlFdTg00XOj6WTg00Xkj7gTf1R0g00YOg00YnR1P1g00ZNR1f0R2g00ZnFgp=:%02#0p=2%12#0p=4%12#1p=6%02#0#0#0p=3g00[NR3g00[lR4#>R5%k4R41S30%C3R6%j3R7P3g00\XR8,\3R9g00]=R:,535<3g00][P9C9':1B71R1P2f2R9g00^BR;g00^bR<'AR=1@29=8;<dAf3:0C]R0b1b2b3W41;2:=832^43P2p,1hR<#Zp,1ER;'YR9#XR>O1b0g00_BR?P3P?P3g00`CP:CVR@9U?3P:%R9P>%Q9%H9%E9%F9%G9%D9%I9%J9R:%K9%L9%M9%N9%O9%P9%08RA#2RB#0#2#TRCp,3sp0RD'?RE%iEp,4brk0RF,?CRC%h:n01100000E000000000000000000000000000000000000000000Ae?3@';=83>ePEPCP9P@CcR?=83>R:eP:P3P?g00aDPEPCP9p,4FULLR9Cb%48#2#6#4#1#6#4#1#2#4#2#7RCg00b;RE%[2#^%>E3_C`X63PDPFp,5rdrawp,3inpP<p,2chP;p,1RP9p,5modelp,3Vspp,4Vbrkp,3Vavp,3Vevp,4Vfitp,2Hhp,2HCPCP@P=P5P4%a3R=P6P3%1A#6#6#2#3#3#3#7RA,53g00c8R@153CR9C9,:7P1P0b1b2b31=ACP2b0P5P4P=P6P3%7BRB,539<39P@%48#1#6#2#1#4#3#3#3#7R8,53C9,:7P1P0b1b2b31;CB/=8P2b0MFdP>P2EWb5o"). Qed.

  Lemma ahm_geom : 4096 <= ps_b05 X /\ ps_b05 X mod 4096 = 0 /\ ps_b05 X + 0x38e000 <= page_down sp0z - 8388608
                   /\ (ps_b05 X + 0x38e000 <= 65536 \/ 7233536 <= ps_b05 X) /\ (ps_b05 X + 0x38e000 <= 2147446784 \/ 17594333495296 <= ps_b05 X).
Proof.
ltac2:(KReplay.run1 (kr_t_AsMainIfaceAHM ()) ["AT_MAIN"] "h01Hh12H0h24__x1h34__x2h44__x3h51Ah61Bh71Ch81Dh91Fh:2H1h;2H2h<2H3h=2H4h>7__arithh?4__ffh@6__sat1hA8__varmaphB5__witp;1p;2p;4p;Cp;3p;7p;8g00c_j1sTg008[j1rTg009bj2\Tg00:`j1PTg00R8j13Tg00Kfj10Tg00R]j17Tg00;`j4MTg00d>j2LTg00e?lCqTg00<@j3lTg00fBj2GTg00Vkj21Tg00OXj3aTg008>j28Tg00LKj1^Tg00Lij2]Tg00fbj1[Tg00gej2CTg00hBR0j22Tg00h]j2YTg00iNj2XTg00ioj1WTg00jHj2VTg00jej2OTg006Sj3?Tg00kBj2NTg00kij2BTg00lEj2QTg00llj2RTg00mRj2STg00n8j2TTg00o<j2UTg005Mj2KTg0000j1pTg000Pj1oTg0010j2HTg00o]j4kTg001Nj1gTg001lj1fTg003:j2FTg002Wj2DTg010;j1cTg003]j3bTg010]j3dTg004@j4ETg004kj2`Tg005gj2_Tg006mj3hTg007Lj4iTg011@j2jTg00Xkj7JTg011Zj8mTg012>j7nTg012bj7ZTf0R1#0#0p=<%31#3p=>%01#0#0#0p=9%01#0#0#0#0#0#0#0p=@g00[NR2g00]=R37?1p==f3R4f2R5'1f1R6/11'jp=6%31#3#3#3p=;P5g00YOR7g00YnR8P8g00ZNR9P2P6g00c8P1CEg00ZnR:FJp=41F21p=:P4P7P8P8P9P5P6P1Gmp=5P5P7P8P8P9P6P1Fnp=IP6P7P8P8P9P1P:FJp=eP5P7P8P8P9P6P1FZp=Ap,3sp0R7p,4brk0p,5rdrawp,3inpp,1hR:p,2chp,1ER;p,1Rp,4FULLp,5modelp,3Vspp,4Vbrkp,3Vavp,3Vevp,2Hhp,2HCg013F#sP2P2%r:/\;#PR<g00\XR=#3R>#3R?#0#<#3#>#0#9#@#7R@CMRA1L:;MCqAl22AR;%0=R:#0#9RB#<#9RC#7RD'G#=RE11D;RFAa22A,8;RA%^B/]7#[R7%0CRC#0#<RB#0#<#9#7RG'CRH'1RIPA%7BRB%3=#0#3#>#<#>#0#9#@#7RJP;C6RKPA%;?#;#;#0#3#>#9#@#7R?%;C#;#;#;#0#<#9#@#7RCP;C6R;'2RA'2RL'2RM'2P0PEPM11D<1G<DRN#=18<@RO/1HPOPBPJP<C6POP?PCP<C6'2'2'2'2ROP1P0PFPLPOP1P0PIPAPOP1P0PKP;POP11Y<D113<113DR0113NRH[[1X<D%=DRP#W1V<DRQ,OD/8N9?2<[1N<D1B3DRR1BND,2HRH[1Q<D1BD31BDN11N3'2[1R<D%=Q\P1S<DA?2N<\Pg013e1T<DRPePPf4RPg014A1U3D'KPReO1PHg00[lRH#p%oHP21H25P61H24Ck%g2%f2RHPH1F23RR1D2=R=54H%c8R8PH%:DRQ94HRP81D2:R:94HRC5C5P8PH%:@9b2=RS%:?54H%:C=4H=5IHRTP8PH%:B94HS%:J=4H=5IHRUP8PH1D2>%:G5d294HSRSP8PHA4HQ=RQP8PHP2P:g00][PRCE,eHRRP8AAHUT9AHS9AHR9AHQC5C5C5C5C5C51`H9P1P5g00^BRHg00^bR9'K1_15=?H9dAh236Cib?bAbBX22X32X4211311134\0[186@P?PCP6C6185@PBPJP5C6184@f5/CG'111DPf6RP#=11DPf7#=18P@R@f8RD/CG'1P@PBPJPPC6P@P?PCPPC6'2'2'2'2[[[[[[^22^32^42P1P7PNP<PDf9f:f>fBfFO9b>b1POeb=b<b;b:b1b0b@X9;X8KP6P1O2n2011000010121000000X0AX7IP6P1O2n2011000010121000000X0LX6FP6P1O2n2011000010121000000X0MX5EP6P1O2n2011000010121000000b0o"). Qed.

  Lemma ahm_zero : forall z, ps_b05 X <= z < ps_b05 X + 0x38e000 -> VM (wa z) = Some (b8 0).
Proof.
ltac2:(KReplay.run1 (kr_t_AsMainIfaceAHM ()) ["AT_MAIN"] "p'0h07__arithh14__ffh28__varmaph35__with41Hh52Hyh62H0h72Hzh84__x1h94__x2h:2H1h;2H2h<2H3h=2H4h>2Hah?6__sat1h@6__sat4hA1yhB2G1hC2G2hD2G3hE2_HhF6__sat0hG1xhH1zi001sp&0p;1p;2p;5p;3p;4p;Hp;Jp;7p;<p;6p;8g008[k10OTg009bk20NTg00:`j1~Tg00R8j13Tg00Kfj10Tg00R]j14Tg008>j22Tg00Vkj27Tg00fBk20MTg00LKj1^Tg00Lij2[Tg00fbk10;Tg00gek205Tg011@j2XTg00hBR0j2=Tg014gj1}Tg015Jj1xTg015lj1JTg00Q6j5LTg016cj1oTg017Zj2nTg006Sj36j1WTg00;`j4STg005Mj2:Tg018<j1iTg019>j2fTg01:Ej2eTg00kij2>Tg01:mj2aTg01;Jj3`Tg00o<j2RTg0000j1_Tg000Pk10LTg00VMk10KTg001Nk10FTg001lk10ETg003:j2BTg01;nk30DTg004kk20=Tg006mk30<Tg007Lj4YTg00P5k40:Tg00c_j15Tg00d>k204Tg00ioj1<Tg01<QR1j1UTg01=1k202Tg01=Tk301Tg01>1j3NTg005gj2|Tg01>Zj4MTg00h]j2{Tg00iNj2wTg00jHj2tTg00jej2sTg00kBj2rTg00lEj2uTg00llj2vTg00mRj2qTg00n8j2pTg0010j2yTg00o]j4zTg002Wj2\Tg003]j3ITg010;k100Tg00<@j3ZTg00<]j1mTg00=]j1lTg00>]k103Tg00?]j1kTg00@]k106Tg00A]k107Tg00B]j1jTg00C]k108Tg00D]k109Tg00E]j1hTg00F]j1gTg00G]k10>Tg00H]k10?Tg00I]k10@Tg00J^k10ATg00MSk10BTg00NYk10CTg00OXj3]Tg01?ElHdTg01@FlJcTg004@j4QTg00Xkj7bTg012bk70GTg01AJm<0HTg01Aok60ITg011Zk80JTf0R2#0#0p=9%32#3p=C%02#0#0#0p=A%02#0#0#0#0#0#0#0p=Df3R3f2R4'7f1R5/>2'=p=1g00[NR6g00]=R7762p=P%32#3#3#3p=;1772p=?P6P5g00c8P2CQp=OP5g00YOR8g00YnR9P9g00ZNR:P2g00ZnFbp=8P6P5g01BSP2CQp=EP4P8P9P9P:P5P2K0Gp=K1>52,=4p=TA6652p=@g01C:R;P6P2P1P5P4P3f4R1f5f6f7R<f8N<0Hp=FP6P5g00][P2CQp=HP5P8P9P9P:P2J0Ip=GP3P8P9P9P:P4P5P2L0Jp=Vp,1hR8$0OR=p,1ER>+0NR?#~R@P2P2g00\XRA#3RB#3RC#0#9#3#C#0#A#D#4RD,2@REC1g01CY%0ARF#9RG#0#9RH#9#ARI#4RJ/7@RK20M@JRL#PRM%^HRNp,3sp0RO'[RP$0;%0IRI#0#9RQ#0#9#A#4+05,7ERR%4Q,7E%3A#0#3#C#9#C#0#A#D#4/7@'X%;C#;#;#0#3#C#A#D#4,7E%;I#;#;#;#0#9#A#D#4/7@'X'=RI'=RC'=RQ'=P0PKPQ%^G#}RG#xRSPPp,4brk0RT,[NRUP?p,4FULLRV%J3DL%o7,nGRG36P2P0PMPCPPPUP?PV%J<DL=6SGP2P0PRPIPPPUP?PVf;R0#JDL=6SGP2POPTp,5rdrawRGp,3inpRSP8p,2chR<P>p,1RR3PVp,5modelRWp,3VspRXp,4VbrkRYp,3VavRZp,3VevR[p,4Vfitp,2HhR\p,2HCR]g01D_g00_BR^P6g00`CP7CSR_PDg00^BR`g00^bRa':Rb%iP/f=%4FR=%4HRH'e1>7=%?H1a=HRc,>7[Rd[%?=Reg01E_RfA`=H5UW>%?c\f^>eP5g014ARe1R7=':O1Pdg00[lRd#_Rf&0LdRd&0K6RH&0F6Rg&0E6Rh1B67Ri1B6DRj'O,8h1B6=Rk>0D6N,Ej,8h3K20=h:R:P2P4PbB0<675RNCYb1b2b3%?D?TDcP2b0b?bFb?PPPUP?P_H0:RcP2P212cDRlC1POPTPGPSP8P<P>P3PVPWPXPYPZP[P\P]g013F#5R]P6P6P@PDCSR\P52048>%5]R>96;]R8#<%4AR[/@=RZ#<%W;RY%W6RX%U5%U2'@A6;5220252401XA;XG;RWP]P[1:6[RVP>P=1:6=M9F9N8ZPfPdPHPg1B6[R8/Hk,8h,GhP:P2P4Pb1|24=6`adPNCYRNb1b2b3g01F;Ra\ZP2b0CM%5>R>96;]RZ#<%4BRB,@[R`#<PYPXPWP]P[PVP>PB1:6BM9F9NZ`PfPdPHPg1B6B,H8,8h,GhP:PNb1b2b3Pa\`P2b0CM%5>#5#5#5#5#5#5#5R>96;]R;#<%CF#4R`,@[RB#<PYPXPWP]P[PVP>P`1:6`M9F9N;BPfPdPHPg1B6`,H8,8h,GhP:PNb1b2b3Pa\BP2b0CM12@7RBP5P512BDRaC1R81{@JR`%?@%?J%?LR;[[R>1w@JRV%PJR[#<1t@JR],sJ/2L,@@[RW1r@JRX1>7JRYAT;LJR;[RZ1u@JRb1>J71>JL17L7'=[Rk1v@JR=%P]\[R]1q@JR31@L@\[R[g013e1p@JRLeR<PLP11R7J,:ePYeO1RYP;PfPdP61y64P5PHCzRHPgPh1\6ARA=I6iRi1\6FRF'O,8hAI6ij,EF,8h5KhRi&009R91OAF,8hAI6Aj,EF,8h5KhRFCVP:PNb1b2b3X86X961227RAP5P512ADC1P5P4P4125DC1[^86^96P2P0P@f9R0O3b0b6P@P0P0PEC1eb=b<b;b:b6b4b@W5P@P4P4PEC1^58eP^P6AZ^6_P7%m?P@%l?&03?%k?&06?&07?%j?&08?&09?R8%h?%g?&0>?&0??&0@?&0A?PP&0BPPU&0C8n01100000E000000000000000000000000000000000000000000A]^6_'2R_P5P512_DR^C1AZ66\R8P4P4A]66\,28C1R8]5ePcP5P5PlC1P8]5eP2O1MHdW5XA6f>R8P@P8P8PEC1REP`P>PVPWPXPZPbPkP=P]P3P[P<PLPYP;PfPdPHPgPhPFP9PiCVP:PNb1b2b3X86X96P2P5P5122DC11257R7P4P4127DC1[^86^96P2fHP@P0O3b0b6PBfFRBPBPaC1eb=b<b;b:b6b4b@W7P_f?R_P_P^C1^7EePcP_P_PlC1^7Eef=O1MJcXEIXDRP5P2O2n2011000000121000000X4CXCMP5P2O2n2011000000121000000X4QXBKP5P2O2n2011000000121000000b4W7XH6o"). Qed.

  Lemma ahm_stk : stk asegs VM (ps_b05 X) (ps_b05 X + 0x38e000).
Proof.
ltac2:(KReplay.run1 (kr_t_AsMainIfaceAHM ()) ["AT_MAIN"] "h01Hh12H0h22H6h34__x1h46__sat4h56__sat5h64__x2h72H1h83H10h92H2h:2H3h;2H4h<2H5h=2H7h>2H8h?2H9h@2HahA7__arithhB4__ffhC8__varmaphD5__withE1ahF4__p1hG4__p2hH4__x3hI4__x4hJ2G1hK2G2hL2G3hM2PDhN2_HhO6__sat6hP6__sat7hQ1bhR2zhp%0p&0p;1p;2p;4p;@p;3p;6p;5p;7p;8g00Kfj10Tg00R]j15Tg008[k10<Tg009bj2zTg00:`j1oTg00Vkj21Tg00fBj2\Tg00R8j14Tg008>j29Tg00LKj1aTg00Lij2`Tg00fbk108Tg00gej2[Tg011@j2ZTg00hBR0j22Tg00Q6j4nk501Tg01FXj4lTg01GSl@kTg00kij23Tg00h]j2VTg00iNj2UTg00ioj1eTg00jHj2_Tg00jej2ITg006Sj3:Tg00kBj2STg00lEj2RTg00llj2QTg00mRj2PTg00n8j2OTg00o<j2TTg005Mj2JTg0000k10@Tg000Pk10?Tg0010j2MTg001Nk10>Tg001lk10=Tg002Wj2GTg010;k10;Tg003:j2]Tg004kk207Tg005gk203Tg006mk302Tg007Lj4~Tg01:Ej2}Tg01:mj2{Tg01;Jj3yTg00c_j1BTg01HVj2YTg01I?j2xTg01Ihj3uTg01JQj1tTg01Joj2sTg01KPj3XTg01L9j2mTg01Lej2pTg00Toj3qTg00VMj1rTg00o]j4LTg01Aoj6vTg01MQj3wTg003]j3WTg010]j3jTg01;nj3iTg014gj1|Tg015Jj1hTg015lk100Tg017Zj2gTg016cj1fTg004@j4HTg01N4k204Tg01O:k405Tg01OTk606Tg00Xkj7dTg011Zk809Tg01PZk30:Tg01QCj6cTg012bj7bTf0R1#0#0p=N%01#0#0p=A%01#0#0#0p==g00[NR2g00]=R37:1p=C%41#4p=E%01#0#0#0#0#0#0#0p=7%41#4#4#4p=>1131p=81]21p=DP2f1R4g00c8P1CHp=<P4g00YOR5g00YnR6P6g00ZNR7P1g00ZnFdp=6f3R8P5P6P6P7f2R9P4P1L09p=;1Y21p=?B0:241p=@P2P4g00][P1CHp=KP4P5P6P6P7P1Ecp=^P9P5P6P6P7P4P1Fbp=Fg01CYg00\XR:#0R;#NS00#AR<#N#=R=#5R>p,1hR?$0<p,1ER@'zS01#oRA'1RB1\A>RC#CRD%4:S02#4RE#A#4#E#0#=#7#5RF,9ARG%a<RHp,3sp0RI'`RJ$08RK%0=R=#ARL#A#=RM#5RN'['1RO%5L,1G%4:#0#4#E#N#E#0#=#7#5/1A'Z%>E#>#>RL#0#4#E#=#7#5,1G%>=#>#>#>#A#=#7#5/1A'Z'2R='2RP'2RQ'2P0PBPQg00aDPJp,4brk0RR,`HS03Q01p,4FULLS04CnRSPAPGClRTP1P0PDPPPTP1P0POP=PTP1PIPRp,5rdrawp,3inpP?p,2chP@p,1RQ04p,5modelp,3Vspp,4Vbrkp,3Vavp,3Vevp,2Hhp,2HCM@k11KJ19K>,3J'2S05%4L#A#=#7#7#7#5RL/1K%7M#7#7#5RM,1K'21\K>R@#CS06'2'2PSPAPG1VA>S07%8ARS%8>R?%8CRR[[S081VK>S09%8K%8@RI\?[S0:1UK>S0;%C>R?#eRT1_K>R0,I>/9@9:2K[RU1SK>RV133>RW13@>,2IRI[RX1RK>RY13>3RZ13>@11@3'2[R[1QK>R\%C0\?R01PK>R]A:2@K\?R@g013eR^1OK>R_eR`P_1UA>Ra1_A>Rb,I>/9C9:2A\TRT1SA>Rc13C>,2RRR\WRd1RA>Re13>C11C3'2\ZRZ1QA>Rf%Cb\?Rg1PA>RhA:2CA\?RiP^1OA>R^eRjP^f4Rkg014ARl1T3>'JPWeRWO1RmPRf;S0<PWO1RWPIg00[lRn$0@Ro&0?nRp1M24&0>2Rq&0=2Rr%D>Rs1G2:Rt'<,6r&0;6Ru1]23Rv/<t,6rC;207r7RwP1P9g00^BRxg00^bRy'J20319=:xydB02234C~RybBbCbDX3211>1%84[^32P1PAfKO2bAb1b2PSeb8b?b>b=b2b<b;b:b9b7b1b0b4b5Q07Q08Q09Q0:%5;RS%5<R<'}133SRx%8<1{S<Rz,33[R{[%8SR|g01E_R}AyS<4UW@%8zR<\}^@|Q0;PUPVPXPYP[P\P0P]P@P`P_PaPTPcPdPePZPfPgPhPiPjP^PmPRPWPIP9P}f@P1P4O2XE|P<^E|fAS0=1T3S,JlPxeO1P{p-0R{g013FRx#BRl#BR|#BR<#BR}#BR~#?%?l1Y2xRx'@'@1x2>=u2x%t:,s2R:%B~#?5X2%?}%?<%?|9X2:'@'@'@'@g01Qg'm'p=qnoPpP21M29RnP4P2%r2R:P81M2kCLCLPqPrPrPrP5P6P6P71Ksv,6rEvPu1G2E9w2s1G2;R;5W2,Kt,6rC;PuPrf6Rs,^r%DLQ02,G2RE'<,6r%DM,<E,6r5Frf7,^r5Fr5FrPuPr%DF9W2tR7%DN9j2E'<,6rPuPr1K;v,6rPu%DS=i2H,<7,6rC;C;C;C;PwPybBbCbDX32X62XH2XI2XF{WGg01F;\?1I>k/999:24[f511L8118M'2/2s'2199F1[kN'1%Ck19kF/1z[[[[^32^62^H2^I2^F{^G{P1Q06Q05PbPKPCPAQ0<fFfHfLO:bAb5b4bRb1b211Gzeb8b?b>b=b2b<b;b:b9b7b1b0b4b5bObP11A1131G'2Q00#a#|Rz%hzPJQ03Q01Q04&009I011gz13:XQz%f3Q07Q08Q09Q0:Q0;PUPVPXPYP[P\P0P]P@P`P_PaPTPcPdPePZPfPgPhPiPjP^PmPRPWPIPoPpP2PnP4P:CLPqPr1<t;,6rP2P;g01BSP7CH,6r5FrRrPuPrC;PwPybBbCbDX32X621114191F,34'21149194F,39'2[^32^62P1fBPAQ0=O3bAb1b2f?R9,1A139G'2eb8b?b>b=b2b<b;b:b9b7b1b0b4b5-044H05W@XE2J06bMXN=XLOP4P1O2n2011000000121000000X0PXKDP4P1O2n2011000000121000000X0QXJBP4P1O2n2011000000121000000b0o"). Qed.
End AT_MAIN.
