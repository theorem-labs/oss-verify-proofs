(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BArr BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BxSymExec3Sound BxSymExec3B BothAcct BothPlanCore BothPlan BothPlanSound BothPlanSoundSums BothInit BothHexScan BsImages BsPlanImages BsHSTab BsStartupHSF BsMainVM BsMainState BsMainFacts BsMainLazyChk BsMainLazy BsMainCells BsMainIface BsMainIfaceKw BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsPlanImagesHex BsPlanImagesHexZ.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsMainSyms.
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

  #[local] Notation lz_facts := (BsMainLazy.facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_lazy := (BsMainLazy.zz_ok_lazy sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_S := (BsMainLazy.zz_ok_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_maps := (BsMainLazy.zz_ok_maps sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_noacc := (BsMainLazy.zz_ok_noacc sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_zr := (BsMainLazy.zz_ok_zr sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation PM_maps_eq := (BsMainLazy.PM_maps_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation PM_lazy_eq := (BsMainLazy.PM_lazy_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation PM_noacc_eq := (BsMainLazy.PM_noacc_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation in_rangesb_zz := (BsMainLazy.in_rangesb_zz sp0 brk0) (only parsing).
  #[local] Notation zin_spec := (BsMainLazy.zin_spec sp0 brk0) (only parsing).

  #[local] Notation kword_main := (BsMainIfaceKw.kword_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  Lemma rw_cells_out : forall m A cs, cells_wf cs -> 0 <= A -> (A + Z.of_nat (cells_size cs) <= 65536 \/ 0x6e8000 <= A) ->
    A + Z.of_nat (cells_size cs) <= 2 ^ 64 -> bytes_at asegs m A (cells_bytes cs) -> rw_cells asegs m A cs.
  Proof.
    intros m A cs WF HA H0 H1 HB. split; [split; [exact WF | exact HB]|].
    apply wr_at_of_some; [lia | lia |]. intros i Hi. destruct HB as (_ & _ & HB).
    pose proof (cells_bytes_length cs WF) as HL.
    specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
    destruct (nth_error (cells_bytes cs) (Z.to_nat i)) as [b|] eqn:Hn; [|apply nth_error_None in Hn; lia].
    exists b. apply (mrd_outside m (A + i) b); [lia | lia | exact HB].
  Qed.
  Lemma obj_word_out : forall a v lo hi, word_check a v = true -> vrange lo hi -> lo <= CXV a -> CXV a + 8 <= hi -> 0 <= lo ->
    (hi <= 65536 \/ 0x6e8000 <= lo) -> hi <= 2 ^ 64 -> rw_cells asegs VM (CXV a) [C8 (wz (CXV v))].
  Proof.
    intros a v lo hi Hc VR H0 H1 H2 H3 H4. apply rw_cells_out; [cbn; tauto | lia | csz; lia | csz; lia |].
    exact (word_main w_all a v Hc (world_ok_all _ _) ltac:(lia) ltac:(lia) (vr_sub _ _ _ _ VR H0 H1)).
  Qed.
  Lemma obj_bytes_out : forall a cs lo hi, bytes_check a (cellsZ cs) = true -> cells_wfb cs = true -> vrange lo hi ->
    lo <= CXV a -> CXV a + Z.of_nat (cells_size cs) <= hi -> 0 <= lo -> (hi <= 65536 \/ 0x6e8000 <= lo) -> hi <= 2 ^ 64 ->
    rw_cells asegs VM (CXV a) cs.
  Proof.
    intros a cs lo hi Hc WF VR H0 H1 H2 H3 H4. apply cells_wfb_sound in WF. apply rw_cells_out; [exact WF | lia | lia | lia |].
    rewrite <- map_b8_cellsZ. apply (bytes_main w_all a (cellsZ cs) Hc (world_ok_all _ _)); rewrite ?(length_cellsZ cs WF); [lia | lia |].
    eapply vr_sub; [exact VR | lia | lia].
  Qed.

  Lemma zero_cells : forall lo hi A cs, (forall z, lo <= z < hi -> VM (wa z) = Some (b8 0)) ->
    cells_wf cs -> cells_bytes cs = repeat (b8 0) (cells_size cs) -> 0 <= lo -> (hi <= 65536 \/ 0x6e8000 <= lo) -> hi <= 2 ^ 64 ->
    lo <= A -> A + Z.of_nat (cells_size cs) <= hi -> rw_cells asegs VM A cs.
  Proof.
    intros lo hi A cs HZ WF HB H0 H1 H2 H3 H4. apply rw_cells_out; [exact WF | lia | lia | lia |]. rewrite HB.
    apply bytes_at_const; [lia | lia |]. intros z Hz. apply HZ. lia.
  Qed.
  Lemma zero_stk : forall lo hi a b, (forall z, lo <= z < hi -> VM (wa z) = Some (b8 0)) -> 0 <= lo -> hi <= 2 ^ 64 ->
    lo <= a -> a <= b -> b <= hi -> stk asegs VM a b.
  Proof. intros lo hi a b HZ H0 H1 H2 H3 H4. apply stk_of_some; [lia | lia |]. intros z Hz. exists (b8 0). apply HZ. lia. Qed.
  Lemma zero_u8arr : forall lo hi a n, (forall z, lo <= z < hi -> VM (wa z) = Some (b8 0)) -> 0 <= lo -> hi <= 2 ^ 64 ->
    lo <= a -> 0 <= n -> a + n <= hi -> u8arr asegs VM a (repeat (b8 0) (Z.to_nat n)).
  Proof. intros lo hi a n HZ H0 H1 H2 H3 H4. apply u8arr_constZ; [lia | lia | lia |]. intros z Hz. apply HZ. lia. Qed.

  Lemma img_stk : forall lo hi, 0x17e000 <= lo -> lo <= hi -> hi <= 0x6e8000 -> stk asegs VM lo hi.
  Proof. intros lo hi H0 H1 H2. apply stk_img_rw; lia. Qed.
  Lemma img_wr : forall a n, 0x17e000 <= a -> a + n <= 0x6e8000 -> wr_at asegs VM a n.
  Proof. intros a n H0 H1. apply wr_at_img_rw; lia. Qed.

  Lemma al_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> aceil = page_down sp0z - 8388608.
  Proof. intros HCEIL Hh'. pose proof pd_facts as (PD1 & PD2 & PD3). unfold aceil. rewrite Hh'. unfold BsMainSyms.page_down in *. lia. Qed.
  Lemma al_top : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> alloc_top (m_vmmaps model) = hceil /\ aceil <= hceil < aceil + 4096.
  Proof.
    intros HCEIL Hh'. pose proof (al_ceil HCEIL Hh') as AC. pose proof pd_facts as (PD1 & PD2 & PD3).
    pose proof (pm_topz _ _ _ _ _ (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)) as T.
    cbn [cfg_model cfg_of] in T. unfold TOP, pm_top in T. rewrite AC, Hh'. lia.
  Qed.
  Definition geo (p : Z * Z) : Prop :=
    fst p mod 4096 = 0 /\ 4096 <= fst p /\ fst p + snd p <= page_down sp0z - 8388608
    /\ (fst p + snd p <= 65536 \/ 7241728 <= fst p) /\ (fst p + snd p <= 2147446784 \/ 17594333495296 <= fst p).
  Lemma al_T   : geo (ps_b09 X, 4096).          Proof. exact (kp_facts _ _ kp_b09). Qed.
  Lemma al_CTX : geo (ps_b10 X, 0x10000).       Proof. exact (kp_facts _ _ kp_b10). Qed.
  Lemma al_R6  : geo (ps_b06 X, 0x2000011000).  Proof. exact (kp_facts _ _ kp_b06). Qed.
  Lemma al_PA  : geo (ps_b08 X, 0x800000).      Proof. exact (kp_facts _ _ kp_b08). Qed.
  Lemma al_FSB : geo (ps_b16 X, 0xb09000).      Proof. exact (kp_facts _ _ kp_b16). Qed.
  Lemma al_D   : geo (ps_b12 X, 4096).          Proof. exact (kp_facts _ _ kp_b12). Qed.
  Lemma al_B11 : geo (ps_b11 X, 4096).          Proof. exact (kp_facts _ _ kp_b11). Qed.

  Lemma al_SB : pm_space_beg X mod 65536 = 0 /\ ps_b06 X < pm_space_beg X <= ps_b06 X + 65536
                /\ pm_region_info X = pm_space_beg X + 2 ^ 37
                /\ pm_region_info X + 4096 <= ps_b06 X + 0x2000011000 /\ 17594333495296 <= ps_b06 X
                /\ ps_b06 X + 0x2000011000 <= page_down sp0z - 8388608.
  Proof.
    pose proof al_R6 as (G1 & G2 & G3 & G4 & G5). cbn [fst snd] in G1, G2, G3, G4, G5. pose proof (pso_spacebeg _ _ _ _ SOK) as [S1 S2].
    unfold pm_region_info. lia.
  Qed.

  Definition zdisj (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.
  Lemma al_apart :
       zdisj (ps_b06 X) 0x2000011000 (ps_b08 X) 0x800000 /\ zdisj (ps_b06 X) 0x2000011000 (ps_b09 X) 4096
    /\ zdisj (ps_b06 X) 0x2000011000 (ps_b10 X) 0x10000 /\ zdisj (ps_b06 X) 0x2000011000 (ps_b16 X) 0xb09000
    /\ zdisj (ps_b06 X) 0x2000011000 (ps_b12 X) 4096
    /\ zdisj (ps_b08 X) 0x800000 (ps_b09 X) 4096 /\ zdisj (ps_b08 X) 0x800000 (ps_b10 X) 0x10000
    /\ zdisj (ps_b08 X) 0x800000 (ps_b16 X) 0xb09000 /\ zdisj (ps_b08 X) 0x800000 (ps_b12 X) 4096
    /\ zdisj (ps_b09 X) 4096 (ps_b10 X) 0x10000 /\ zdisj (ps_b09 X) 4096 (ps_b16 X) 0xb09000 /\ zdisj (ps_b09 X) 4096 (ps_b12 X) 4096
    /\ zdisj (ps_b10 X) 0x10000 (ps_b16 X) 0xb09000 /\ zdisj (ps_b10 X) 0x10000 (ps_b12 X) 4096
    /\ zdisj (ps_b16 X) 0xb09000 (ps_b12 X) 4096.
  Proof.
    unfold zdisj.
    pose proof (kp_apart_ne 2 3 _ _ ltac:(lia) kp_b06 kp_b08) as A1. pose proof (kp_apart_ne 2 4 _ _ ltac:(lia) kp_b06 kp_b09) as A2.
    pose proof (kp_apart_ne 2 5 _ _ ltac:(lia) kp_b06 kp_b10) as A3. pose proof (kp_apart_ne 2 8 _ _ ltac:(lia) kp_b06 kp_b16) as A4.
    pose proof (kp_apart_ne 2 7 _ _ ltac:(lia) kp_b06 kp_b12) as A5.
    pose proof (kp_apart_ne 3 4 _ _ ltac:(lia) kp_b08 kp_b09) as A6. pose proof (kp_apart_ne 3 5 _ _ ltac:(lia) kp_b08 kp_b10) as A7.
    pose proof (kp_apart_ne 3 8 _ _ ltac:(lia) kp_b08 kp_b16) as A8. pose proof (kp_apart_ne 3 7 _ _ ltac:(lia) kp_b08 kp_b12) as A9.
    pose proof (kp_apart_ne 4 5 _ _ ltac:(lia) kp_b09 kp_b10) as A10. pose proof (kp_apart_ne 4 8 _ _ ltac:(lia) kp_b09 kp_b16) as A11.
    pose proof (kp_apart_ne 4 7 _ _ ltac:(lia) kp_b09 kp_b12) as A12.
    pose proof (kp_apart_ne 5 8 _ _ ltac:(lia) kp_b10 kp_b16) as A13. pose proof (kp_apart_ne 5 7 _ _ ltac:(lia) kp_b10 kp_b12) as A14.
    pose proof (kp_apart_ne 8 7 _ _ ltac:(lia) kp_b16 kp_b12) as A15'.
    cbn [fst snd] in *. repeat split; assumption.
  Qed.

  Lemma al_stack : pm_stack_top sp0z mod 4096 = 0 /\ sp0z - 160 <= pm_stack_top sp0z < sp0z - 160 + 4096
                   /\ 0x7fff80000000 <= pm_stack_top sp0z <= 0x800000000000 /\ pm_stack_bottom sp0z = pm_stack_top sp0z - 8388608.
  Proof.
    pose proof pd_facts as (PD1 & PD2 & PD3). pose proof lz_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VSP).
    unfold pm_stack_bottom, pm_stack_top, BsMainSyms.page_up. unfold BsMainSyms.page_down in *.
    split; [apply Z_mod_mult|].
    pose proof (Z.div_mod (sp0z - 160 + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0z - 160 + 4095) 4096 ltac:(lia)).
    assert (sp0z / 4096 <= (sp0z - 160 + 4095) / 4096) by (apply Z.div_le_mono; lia). lia.
  Qed.

  Definition al_lits : list (Z * list cell) :=
    [ (0x18d9d8 + 40, [C4 (wz 0xffffffff); C4 (wz 0)]);
      (0x18d9d8 + 56, [C8 (wz 0); C8 (wz 4096)]);
      (0x18d9d8 + 88, [C8 (wz 0x800000)]);
      (0x18d9d8 + 112, [C8 (wz 0); C8 (wz 0); C8 (wz 0)]);
      (0x18d9d8 + 680, [C8 (wz 0)]);
      (0x18d9d8 + 792, [C8 (wz 0x10000000); C8 (wz 0xE666661); C8 (wz 0x100000)]);
      (0x18d9d8 + 880, [C8 (wz 0)]);
      (0x18d9d8 + 888, [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]);
      (0x18d9d8 + 984, [C8 (wz 0)]);
      (0x18d9d8 + 3616, [C8 (wz (2 ^ 40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]]);
      (0x18e838 + 44, [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)]);
      (0x18e838 + 78, [C1 (b8 1)]); (0x18e838 + 85, [C1 (b8 1)]); (0x18e838 + 88, [C1 (b8 1)]);
      (0x222b68 + 34, [C1 (b8 1)]); (0x222b68 + 120, [C8 (wz 0xffffffffffffffff)]); (0x222b68 + 144, [C8 (wz 0)]); (0x222b68 + 260, [C1 (b8 0)]);
      (0x222b68 + 219, [C1 (b8 1)]); (0x222b68 + 244, [C1 (b8 1)]);
      (0x191038, [C8 (wz 0x7fff8000)]);
      (0x191d20, [C8 (wz (2 ^ 47 - 1)); C8 (wz 0); C8 (wz 0)]);
      (0x19089c, [C1 (b8 1)]);
      (0x191d18, [C1 (b8 1)]);
      (0x191d3c, [C4 (wz 30)]);
      (0x1908a0, [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)]);
      (0x2132a0, [C1 (b8 0); C1 (b8 1); C1 (b8 0)]);
      (0x220ac8, [C1 (b8 0); C1 (b8 0); C2 (wz 0)]);
      (0x222b00, [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]);
      (0x222b5c, [C4 (wz 0)]);
      (0x187148, [C8 (wz 0x176ea4)]);
      (0x185080, map (fun v => C8 (wz v))
         [0x220ae0; 0x187180; 0x222b68; 0x18e838; 0x191038; 0x191d28; 0x191d30; 0x191d20; 0x187148; 0x187140; 0x187178; 0x187190; 1; 0x222b5c; 0x220ad8]);

      (0x220ae0, [C8 (wz 4096)]);
      (0x187180, [C8 (wz 0x1ae42)]);
      (0x187190, [C8 (wz 0x23106)]);
      (0x6c5800, [C8 (wz 0x6e6d10)]);
      (0x6c5868, [C4 (wz 0)]);
      (0x185d00, [C8 (wz 0x10)]);
      (0x6e5b18, [C8 (wz 4096)]);
      (0x185ed0, [C8 (wz 0x6e5898)]) ].
  Lemma al_lits_check : forallb (fun ac => img_cells_check (fst ac) (snd ac)) al_lits = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma al_lits_main : Forall (fun ac => rw_cells asegs VM (fst ac) (snd ac)) al_lits.
  Proof. apply Forall_forall. intros ac Hin. apply img_cells_main. exact (proj1 (forallb_forall _ _) al_lits_check ac Hin). Qed.

  Lemma al_lit : forall A cs, In (A, cs) al_lits -> rw_cells asegs VM A cs.
  Proof. intros A cs Hin. exact (proj1 (Forall_forall _ _) al_lits_main (A, cs) Hin). Qed.
  Ltac inlits := cbv beta delta [al_lits In map]; repeat (first [left; reflexivity | right]).

  Lemma in_releasems : rw_cells asegs VM (0x18d9d8 + 40) [C4 (wz 0xffffffff); C4 (wz 0)].                      Proof. apply al_lit; inlits. Qed.
  Lemma in_premapped : rw_cells asegs VM (0x18d9d8 + 56) [C8 (wz 0); C8 (wz 4096)].                             Proof. apply al_lit; inlits. Qed.
  Lemma in_ptrsize   : rw_cells asegs VM (0x18d9d8 + 88) [C8 (wz 0x800000)].                                      Proof. apply al_lit; inlits. Qed.
  Lemma in_nreserved : rw_cells asegs VM (0x18d9d8 + 112) [C8 (wz 0); C8 (wz 0); C8 (wz 0)].                     Proof. apply al_lit; inlits. Qed.
  Lemma in_secmutex  : rw_cells asegs VM (0x18d9d8 + 680) [C8 (wz 0)].                                            Proof. apply al_lit; inlits. Qed.
  Lemma in_quar      : rw_cells asegs VM (0x18d9d8 + 792) [C8 (wz 0x10000000); C8 (wz 0xE666661); C8 (wz 0x100000)]. Proof. apply al_lit; inlits. Qed.
  Lemma in_qmutex    : rw_cells asegs VM (0x18d9d8 + 880) [C8 (wz 0)].                                            Proof. apply al_lit; inlits. Qed.
  Lemma in_gq        : rw_cells asegs VM (0x18d9d8 + 888) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].         Proof. apply al_lit; inlits. Qed.
  Lemma in_fbmutex   : rw_cells asegs VM (0x18d9d8 + 984) [C8 (wz 0)].                                            Proof. apply al_lit; inlits. Qed.
  Lemma in_maxuser   : rw_cells asegs VM (0x18d9d8 + 3616) [C8 (wz (2 ^ 40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]].
  Proof. apply al_lit; inlits. Qed.

  Lemma fl_fill      : rw_cells asegs VM (0x18e838 + 44) [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)].  Proof. apply al_lit; inlits. Qed.
  Lemma fl_psg       : rw_cells asegs VM (0x18e838 + 78) [C1 (b8 1)].                                Proof. apply al_lit; inlits. Qed.
  Lemma fl_pp        : rw_cells asegs VM (0x18e838 + 85) [C1 (b8 1)].                                Proof. apply al_lit; inlits. Qed.
  Lemma fl_ndtm      : rw_cells asegs VM (0x18e838 + 88) [C1 (b8 1)].                                Proof. apply al_lit; inlits. Qed.
  Lemma fl_fastuw    : rw_cells asegs VM (0x222b68 + 34) [C1 (b8 1)].                                Proof. apply al_lit; inlits. Qed.
  Lemma fl_csmt      : rw_cells asegs VM (0x222b68 + 120) [C8 (wz 0xffffffffffffffff)].                         Proof. apply al_lit; inlits. Qed.
  Lemma fl_mmaplim   : rw_cells asegs VM (0x222b68 + 144) [C8 (wz 0)].                               Proof. apply al_lit; inlits. Qed.
  Lemma fl_decorate  : rw_cells asegs VM (0x222b68 + 260) [C1 (b8 0)].                               Proof. apply al_lit; inlits. Qed.
  Lemma fl_c219      : rw_cells asegs VM (0x222b68 + 219) [C1 (b8 1)].                               Proof. apply al_lit; inlits. Qed.
  Lemma fl_c244      : rw_cells asegs VM (0x222b68 + 244) [C1 (b8 1)].                               Proof. apply al_lit; inlits. Qed.
  Lemma fl_shbase    : rw_cells asegs VM 0x191038 [C8 (wz 0x7fff8000)].                               Proof. apply al_lit; inlits. Qed.
  Lemma fl_highend   : rw_cells asegs VM 0x191d20 [C8 (wz (2 ^ 47 - 1)); C8 (wz 0); C8 (wz 0)].       Proof. apply al_lit; inlits. Qed.
  Lemma fl_canpoison : rw_cells asegs VM 0x19089c [C1 (b8 1)].                                         Proof. apply al_lit; inlits. Qed.
  Lemma fl_inited    : rw_cells asegs VM 0x191d18 [C1 (b8 1)].                                         Proof. apply al_lit; inlits. Qed.
  Lemma fl_ctxsize   : rw_cells asegs VM 0x191d3c [C4 (wz 30)].                                        Proof. apply al_lit; inlits. Qed.
  Lemma fl_tsdinit   : rw_cells asegs VM 0x1908a0 [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)].    Proof. apply al_lit; inlits. Qed.
  Lemma fl_allocfl   : rw_cells asegs VM 0x2132a0 [C1 (b8 0); C1 (b8 1); C1 (b8 0)].                  Proof. apply al_lit; inlits. Qed.
  Lemma fl_iainit    : rw_cells asegs VM 0x220ac8 [C1 (b8 0); C1 (b8 0); C2 (wz 0)].                  Proof. apply al_lit; inlits. Qed.
  Lemma fl_hooks     : rw_cells asegs VM 0x222b00 (repeat (C8 (wz 0)) 10).                             Proof. apply al_lit; inlits. Qed.
  Lemma fl_dying     : rw_cells asegs VM 0x222b5c [C4 (wz 0)].                                         Proof. apply al_lit; inlits. Qed.
  Lemma fl_realms    : rw_cells asegs VM 0x187148 [C8 (wz 0x176ea4)].                                  Proof. apply al_lit; inlits. Qed.
  Lemma fl_got       : rw_cells asegs VM 0x185080 (map (fun v => C8 (wz v))
                         [0x220ae0; 0x187180; 0x222b68; 0x18e838; 0x191038; 0x191d28; 0x191d30; 0x191d20; 0x187148; 0x187140; 0x187178; 0x187190; 1; 0x222b5c; 0x220ad8]).
  Proof. apply al_lit; inlits. Qed.
  Lemma fl_pagesz    : rw_cells asegs VM 0x220ae0 [C8 (wz 4096)].                                      Proof. apply al_lit; inlits. Qed.
  Lemma fl_secname   : rw_cells asegs VM 0x187180 [C8 (wz 0x1ae42)].                                   Proof. apply al_lit; inlits. Qed.
  Lemma fl_primname  : rw_cells asegs VM 0x187190 [C8 (wz 0x23106)].                                   Proof. apply al_lit; inlits. Qed.
  Lemma fl_tlsslot   : rw_cells asegs VM 0x6c5800 [C8 (wz 0x6e6d10)].                                  Proof. apply al_lit; inlits. Qed.
  Lemma fl_lsandis   : rw_cells asegs VM 0x6c5868 [C4 (wz 0)].                                         Proof. apply al_lit; inlits. Qed.
  Lemma fl_got2      : rw_cells asegs VM 0x185d00 [C8 (wz 0x10)].                                      Proof. apply al_lit; inlits. Qed.
  Lemma fx_libcpgsz  : rw_cells asegs VM 0x6e5b18 [C8 (wz 4096)].                                      Proof. apply al_lit; inlits. Qed.
  Lemma fx_gotssp    : rw_cells asegs VM 0x185ed0 [C8 (wz 0x6e5898)].                                  Proof. apply al_lit; inlits. Qed.

  Lemma fx_canary : exists gd : word, rw_cells asegs VM 0x6e5898 [C8 gd].
  Proof.
    exists (edenot E (EVar 61)).
    pose proof (kword_main w_all (CAbs, 0x6e5898) 8 (EVar 61) ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)) as W.
    revert W. pmc_simpl. rewrite Z.add_0_l. intros W.
    apply rw_cells_img; [cbn; tauto | lia | csz; lia |]. apply bytes_at_of_nth; [lia | csz; lia |]. intros i Hi.
    apply (rdn_mrd ASEGS (cells_bytes [C8 (edenot E (EVar 61))]) VM 0x6e5898); [| lia | csz; lia | exact Hi].
    cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact (W ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)).
  Qed.

  Lemma in_spacebeg : rw_cells asegs VM (0x18d9d8 + 32) [C8 (wz (pm_space_beg X))].
  Proof.
    replace (pm_space_beg X) with (CXV (CRI, - 2 ^ 37)) by (pmc_simpl; unfold pm_region_info; lia).
    apply (img_word_main (0x18d9d8 + 32) (CRI, - 2 ^ 37) ltac:(vm_cast_no_check (@eq_refl bool true))); lia.
  Qed.
  Lemma in_regioninfo : rw_cells asegs VM (0x18d9d8 + 48) [C8 (wz (pm_region_info X))].
  Proof. replace (pm_region_info X) with (CXV (CRI, 0)) by (pmc_simpl; lia). apply (img_word_main (0x18d9d8 + 48) (CRI, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.
  Lemma in_chunks : rw_cells asegs VM (0x18d9d8 + 72) [C8 (wz (ps_b08 X))].
  Proof. replace (ps_b08 X) with (CXV (CB08, 0)) by (pmc_simpl; lia). apply (img_word_main (0x18d9d8 + 72) (CB08, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.
  Lemma in_ptrbase : rw_cells asegs VM (0x18d9d8 + 80) [C8 (wz (ps_b08 X))].
  Proof. replace (ps_b08 X) with (CXV (CB08, 0)) by (pmc_simpl; lia). apply (img_word_main (0x18d9d8 + 80) (CB08, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.

  Lemma in_hdr : rw_cells asegs VM (0x18d9d8 + 32)
    [C8 (wz (pm_space_beg X)); C4 (wz 0xffffffff); C4 (wz 0); C8 (wz (pm_region_info X)); C8 (wz 0); C8 (wz 4096);
     C8 (wz (ps_b08 X)); C8 (wz (ps_b08 X)); C8 (wz 0x800000)].
  Proof.
    apply rw_cells_cons1; [exact in_spacebeg|]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (proj2 (rw_cells_app asegs VM _ [C4 (wz 0xffffffff); C4 (wz 0)] _)). split; [exact in_releasems|]. csz.
    apply rw_cells_cons1; [exact in_regioninfo|]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ].
    apply (proj2 (rw_cells_app asegs VM _ [C8 (wz 0); C8 (wz 4096)] _)). split; [exact in_premapped|]. csz.
    apply rw_cells_cons1; [exact in_chunks|]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ].
    apply rw_cells_cons1; [exact in_ptrbase|]. cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ]. exact in_ptrsize.
  Qed.

  Lemma fl_tsd : rw_cells asegs VM 0x6e6d10 [C8 (wz (ps_b10 X))].
  Proof. replace (ps_b10 X) with (CXV (CB10, 0)) by (pmc_simpl; lia). apply (img_word_main 0x6e6d10 (CB10, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.

  Lemma ia_zero_scan : BothHexTree.zpt AsanUbsan_seg_bytes_003 (Z.to_N (0x192240 - 0x186000)) (Z.to_N 0x81030).
  Proof. exact BsPlanImagesHexZ.asan_ia_zero. Qed.
  Lemma seg_rom_bss_ia : forall z, 0x192240 <= z < 0x213270 -> BPropExec.seg_rom ASEGS (wa z) = Some (b8 0).
  Proof.
    intros z Hz. unfold BPropExec.seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
    replace (find_segment ASEGS z 1) with (Some AsanUbsan_segment_003).
    2:{ rewrite asan_segs_eq. cbn -[Z.leb Z.add Z.of_N]. cbn [Z.of_N seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002 AsanUbsan_segment_003].
        destruct (Z.leb_spec 65536 z); destruct (Z.leb_spec (z + 1) (65536 + 528384)); cbn [andb]; try lia;
        destruct (Z.leb_spec 593920 z); destruct (Z.leb_spec (z + 1) (593920 + 970752)); cbn [andb]; try lia;
        destruct (Z.leb_spec 1564672 z); destruct (Z.leb_spec (z + 1) (1564672 + 32768)); cbn [andb]; try lia;
        destruct (Z.leb_spec 1597440 z); destruct (Z.leb_spec (z + 1) (1597440 + 5644288)); cbn [andb]; try lia. reflexivity. }
    replace (seg_readable AsanUbsan_segment_003) with true by reflexivity.
    cbn [seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes AsanUbsan_segment_003].
    change (Z.of_N 1597440%N) with 1597440.
    cbn [AsanUbsan_segment_003 seg_bytes]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    match goal with |- context [segment_byte_at ?l ?o] => replace (segment_byte_at l o) with (Some (b8 0)); [reflexivity|] end.
    symmetry. eapply (BothHexTree.segment_byte_at_zero_pt _ _ _ _ ia_zero_scan); [rewrite asan_len3; cbn; lia | lia].
  Qed.
  Lemma ia_pristine : forall z, 0x192240 <= z < 0x213270 -> VM (wa z) = None /\ mrd asegs VM (wa z) = Some (b8 0).
  Proof.
    intros z Hz. pose proof (pmc_img _ _ _ _ _ _ MC 0x192240 0x213270 ltac:(vm_cast_no_check (@eq_refl bool true)) z Hz) as HN. fold (wa z) in HN.
    rewrite (vm_img z ltac:(lia)). split; [exact HN|]. unfold mrd. rewrite (vm_img z ltac:(lia)), HN, seg_rom_lib, asegs_ASEGS. apply seg_rom_bss_ia. exact Hz.
  Qed.
  Lemma ia_main : u8arr asegs VM 0x192240 (repeat (b8 0) (Z.to_nat 0x81030)).
  Proof.
    split; [| rewrite repeat_length, Z2Nat.id by lia; apply img_wr; lia].
    apply bytes_at_of_nth; [lia | rewrite repeat_length, Z2Nat.id by lia; lia |]. intros i Hi. rewrite repeat_length in Hi.
    rewrite (nth_error_repeat (b8 0) Hi). apply (proj2 (ia_pristine (0x192240 + Z.of_nat i) ltac:(lia))).
  Qed.

  #[local] Notation T := (ps_b09 X).
  #[local] Notation CTX := (ps_b10 X).
  Ltac geoT := pose proof al_T as (GT1 & GT2 & GT3 & GT4 & GT5); pose proof pd_facts as (PD1 & PD2 & PD3); cbn [fst snd] in GT1, GT2, GT3, GT4, GT5.
  Lemma th_ctx : rw_cells asegs VM T [C8 (wz CTX)].
  Proof.
    geoT. pose proof (obj_word_out (CB09, 0) (CB10, 0) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b09) as W. revert W. pmc_simpl. rewrite !Z.add_0_r. intros W. apply W; lia.
  Qed.
  Lemma th_stack : rw_cells asegs VM (T + 8) [C8 (wz (pm_stack_top sp0z)); C8 (wz (pm_stack_top sp0z - 8388608))].
  Proof.
    geoT. apply rw_cells_cons1; cbn [csize Z.of_nat Pos.of_succ_nat Pos.succ].
    - pose proof (obj_word_out (CB09, 8) (CSTK, 0) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b09) as W. revert W. pmc_simpl. rewrite !Z.add_0_r. intros W. apply W; lia.
    - pose proof (obj_word_out (CB09, 16) (CSTK, - 8388608) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b09) as W. revert W. pmc_simpl. intros W.
      replace (pm_stack_top sp0z - 8388608) with (pm_stack_top sp0z + - 8388608) by lia. match goal with |- rw_cells _ _ ?a _ => replace a with (T + 16) by lia end. apply W; lia.
  Qed.
  Lemma th_w24 : rw_cells asegs VM (T + 24) [C8 (wz 0); C8 (wz 0)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 24) [C8 (wz 0); C8 (wz 0)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_b40 : rw_cells asegs VM (T + 40) [C1 (b8 0)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 40) [C1 (b8 0)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_zero41 : forall z, T + 41 <= z < T + 48 -> VM (wa z) = Some (b8 0).
  Proof. geoT. pose proof (obj_zero_main (CB09, 41) 7 _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) (fun z Hz => proj1 (vr_b09 z Hz))) as W. revert W. pmc_simpl. intros W z Hz. apply W; lia. Qed.
  Lemma th_tls : rw_cells asegs VM (T + 48) [C8 (wz 0x6c5f90); C8 (wz 0x6c606c)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 48) [C8 (wz 0x6c5f90); C8 (wz 0x6c606c)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_dtv : rw_cells asegs VM (T + 64) [C8 (wz 0x6c5860)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 64) [C8 (wz 0x6c5860)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_fs : rw_cells asegs VM (T + 72) [C8 (wz (ps_b16 X))].
  Proof. geoT. pose proof (obj_word_out (CB09, 72) (CB16, 0) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b09) as W. revert W. pmc_simpl. rewrite !Z.add_0_r. intros W. apply W; lia. Qed.
  Lemma th_zero80 : forall z, T + 80 <= z < T + 3168 -> VM (wa z) = Some (b8 0).
  Proof. geoT. pose proof (obj_zero_main (CB09, 80) 3088 _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) (fun z Hz => proj1 (vr_b09 z Hz))) as W. revert W. pmc_simpl. intros W z Hz. apply W; lia. Qed.
  Lemma th_unw : rw_cells asegs VM (T + 3168) [C1 (b8 0)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 3168) [C1 (b8 0)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_zero3169 : forall z, T + 3169 <= z < T + 4096 -> VM (wa z) = Some (b8 0).
  Proof. geoT. pose proof (obj_zero_main (CB09, 3169) 927 _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) (fun z Hz => proj1 (vr_b09 z Hz))) as W. revert W. pmc_simpl. intros W z Hz. apply W; lia. Qed.

  Lemma th_tq : rw_cells asegs VM (T + 80) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
  Proof. geoT. apply (zero_cells _ _ _ _ th_zero80); [cbn; tauto | reflexivity | lia | lia | lia | lia | csz; lia]. Qed.
  Lemma th_cells0 : forall A cs, cells_wf cs -> cells_bytes cs = repeat (b8 0) (cells_size cs) ->
    T + 80 <= A -> A + Z.of_nat (cells_size cs) <= T + 3168 -> rw_cells asegs VM A cs.
  Proof. intros A cs WF HB H0 H1. geoT. apply (zero_cells _ _ _ _ th_zero80); try assumption; lia. Qed.
  Lemma th_stk80 : forall a b, T + 80 <= a -> a <= b -> b <= T + 3168 -> stk asegs VM a b.
  Proof. intros a b H0 H1 H2. geoT. apply (zero_stk _ _ _ _ th_zero80); lia. Qed.
  Lemma th_u8z80 : forall a n, T + 80 <= a -> 0 <= n -> a + n <= T + 3168 -> u8arr asegs VM a (repeat (b8 0) (Z.to_nat n)).
  Proof. intros a n H0 H1 H2. geoT. apply (zero_u8arr _ _ _ _ th_zero80); lia. Qed.
  Lemma th_cells0_hi : forall A cs, cells_wf cs -> cells_bytes cs = repeat (b8 0) (cells_size cs) ->
    T + 3169 <= A -> A + Z.of_nat (cells_size cs) <= T + 4096 -> rw_cells asegs VM A cs.
  Proof. intros A cs WF HB H0 H1. geoT. apply (zero_cells _ _ _ _ th_zero3169); try assumption; lia. Qed.
  Lemma th_stk3169 : forall a b, T + 3169 <= a -> a <= b -> b <= T + 4096 -> stk asegs VM a b.
  Proof. intros a b H0 H1 H2. geoT. apply (zero_stk _ _ _ _ th_zero3169); lia. Qed.
  Lemma th_stk41 : forall a b, T + 41 <= a -> a <= b -> b <= T + 48 -> stk asegs VM a b.
  Proof. intros a b H0 H1 H2. geoT. apply (zero_stk _ _ _ _ th_zero41); lia. Qed.

  Lemma cx_tid : rw_cells asegs VM (CTX + 8) [C4 (wz 0)].
  Proof.
    pose proof al_CTX as (G1 & G2 & G3 & G4 & G5). cbn [fst snd] in G1, G2, G3, G4, G5. pose proof pd_facts as (PD1 & PD2 & PD3).
    pose proof (obj_bytes_out (CB10, 8) [C4 (wz 0)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b10) as W. revert W. pmc_simpl. csz. intros W. apply W; lia.
  Qed.
  Lemma cx_thr : rw_cells asegs VM (CTX + 152) [C8 (wz T)].
  Proof.
    pose proof al_CTX as (G1 & G2 & G3 & G4 & G5). cbn [fst snd] in G1, G2, G3, G4, G5. pose proof pd_facts as (PD1 & PD2 & PD3).
    pose proof (obj_word_out (CB10, 152) (CB09, 0) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b10) as W. revert W. pmc_simpl. rewrite !Z.add_0_r. intros W. apply W; lia.
  Qed.

  Lemma ri_zero : forall z, pm_region_info X <= z < pm_region_info X + 4096 -> VM (wa z) = Some (b8 0).
  Proof.
    pose proof (obj_zero_main (CRI, 0) 4096 _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vm_ri) as W. revert W. pmc_simpl. rewrite !Z.add_0_r. intros W z Hz. apply W; lia.
  Qed.
  Lemma ri_cells0 : forall A cs, cells_wf cs -> cells_bytes cs = repeat (b8 0) (cells_size cs) ->
    pm_region_info X <= A -> A + Z.of_nat (cells_size cs) <= pm_region_info X + 4096 -> rw_cells asegs VM A cs.
  Proof. intros A cs WF HB H0 H1. pose proof al_SB as SB. pose proof pd_facts as (PD1 & PD2 & PD3). apply (zero_cells _ _ _ _ ri_zero); try assumption; lia. Qed.
  Lemma ri_stk : forall a b, pm_region_info X <= a -> a <= b -> b <= pm_region_info X + 4096 -> stk asegs VM a b.
  Proof. intros a b H0 H1 H2. pose proof al_SB as SB. pose proof pd_facts as (PD1 & PD2 & PD3). apply (zero_stk _ _ _ _ ri_zero); lia. Qed.
  Lemma ri_u8z : forall a n, pm_region_info X <= a -> 0 <= n -> a + n <= pm_region_info X + 4096 -> u8arr asegs VM a (repeat (b8 0) (Z.to_nat n)).
  Proof. intros a n H0 H1 H2. pose proof al_SB as SB. pose proof pd_facts as (PD1 & PD2 & PD3). apply (zero_u8arr _ _ _ _ ri_zero); lia. Qed.
  Lemma pa_empty : u64arr asegs VM (ps_b08 X) [] /\ wr_at asegs VM (ps_b08 X) 0.
  Proof.
    pose proof al_PA as (G1 & G2 & G3 & G4 & G5). cbn [fst snd] in G1, G2, G3, G4, G5. pose proof pd_facts as (PD1 & PD2 & PD3).
    unfold u64arr, bytes_at, wr_at. cbn [u64s length Z.of_nat Z.mul flat_map]. repeat split; try lia; intros i Hi; lia.
  Qed.

  Lemma athr_cells_main : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> athr_cells VM.
  Proof.
    intros HCEIL Hh'. pose proof (al_ceil HCEIL Hh') as AC. geoT.
    pose proof al_CTX as (C1' & C2 & C3 & C4' & C5). cbn [fst snd] in C1', C2, C3, C4', C5.
    pose proof al_D as (D1 & D2 & D3 & D4 & D5). cbn [fst snd] in D1, D2, D3, D4, D5.
    exists CTX, T, (ps_b12 X), (wz 0x6c5f90), (wz 0x6c606c).
    split; [exact fl_tsd|]. split; [exact cx_thr|]. split; [exact th_tls|].
    split. { pose proof (img_word_main (ATP + 8) (CB12, 0) ltac:(vm_cast_no_check (@eq_refl bool true))) as W. revert W. pmc_simpl. rewrite Z.add_0_r. intros W. apply W; unfold ATP; lia. }
    split. { pose proof (obj_word_out (CB12, 24) (CAbs, ATP) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b12) as W. revert W. pmc_simpl. rewrite Z.add_0_l. intros W. apply W; unfold ATP; lia. }
    rewrite AC. lia.
  Qed.

  #[local] Notation VMM := (m_vmmaps model).
  #[local] Notation PMo := (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
  Lemma ak_limit : vm_limit VMM = target_alloc_limit.
  Proof. exact (pm_limit _ _ _ _ _ PMo). Qed.
  Lemma ak_top : alloc_top VMM = sp0z - 8388608.
  Proof. pose proof (pm_topz _ _ _ _ _ PMo) as T0. cbn [cfg_model cfg_of] in T0. unfold TOP, pm_top in T0. exact T0. Qed.
  Lemma ak_eager : eager_used model <= 16519168.
  Proof. pose proof (pm_eager _ _ _ _ _ PMo) as EG. cbn [cfg_model cfg_of] in EG. assert (H16 : 16515072 <= 16519168) by lia. exact (Z.le_trans _ _ _ EG H16). Qed.
  Lemma ak_reserved : vm_reserved VMM = segments_reserved ASEGS.
  Proof. exact (pm_reserved _ _ _ _ _ PMo). Qed.
  Lemma ak_res_list : segments_reserved ASEGS =
    [(Z_to_bv 64 0x10000, Z_to_bv 64 0x81000); (Z_to_bv 64 0x91000, Z_to_bv 64 0xed000); (Z_to_bv 64 0x17e000, Z_to_bv 64 0x8000); (Z_to_bv 64 0x186000, Z_to_bv 64 0x562000)].
  Proof. vm_compute. reflexivity. Qed.
  Lemma ak_maps : vm_maps VMM = zz2ww (PM_MAPS brk0z X).        Proof. exact PM_maps_eq. Qed.
  Lemma ak_noacc : vm_noaccess VMM = zz2ww (PM_NOACC brk0z X).  Proof. exact PM_noacc_eq. Qed.
  Lemma ak_lazy : m_vm_lazy model = zz2ww (PM_LAZY sp0z X).       Proof. exact PM_lazy_eq. Qed.

  Lemma ak1 : forall e, In e (vm_reserved VMM) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= 0x6e8000.
  Proof. intros e He. rewrite ak_reserved in He. pose proof (proj1 (Forall_forall _ _) asan_res_hull e He) as [_ H2]. cbn [img_hi ASAN_H] in H2. exact H2. Qed.
  Lemma ak1_lo : forall e, In e (vm_reserved VMM) -> 0x10000 <= bv_unsigned (fst e).
  Proof. intros e He. rewrite ak_reserved in He. pose proof (proj1 (Forall_forall _ _) asan_res_hull e He) as [H1 _]. cbn [img_lo ASAN_H] in H1. exact H1. Qed.
  Lemma ak9 : forall x : word, 0x10000 <= bv_unsigned x < 0x6e8000 -> in_rangesb x (vm_reserved VMM) = true.
  Proof.
    intros x Hx. rewrite ak_reserved. destruct (proj2 asan_res_cover (bv_unsigned x) ltac:(cbn [img_lo img_hi ASAN_H]; lia)) as [iv [Hin Hr]].
    unfold in_rangesb. apply existsb_exists. exists iv. split; [exact Hin|]. unfold zin_rangeb. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma zz_in : forall l x b k, zz_ok l -> In (b, k) l -> b <= bv_unsigned x < b + k -> in_rangesb x (zz2ww l) = true.
  Proof. intros l x b k Hl Hin Hx. rewrite (in_rangesb_zz l x Hl). apply (proj2 (zin_spec _ _)). exists (b, k). cbn [fst snd]. split; [exact Hin | lia]. Qed.
  Lemma zz_cases : forall l x, zz_ok l -> in_rangesb x (zz2ww l) = true -> exists p, In p l /\ fst p <= bv_unsigned x < fst p + snd p.
  Proof. intros l x Hl H. rewrite (in_rangesb_zz l x Hl) in H. exact (proj1 (zin_spec _ _) H). Qed.
  Lemma zz_out : forall l x, zz_ok l -> (forall p, In p l -> ~ (fst p <= bv_unsigned x < fst p + snd p)) -> in_rangesb x (zz2ww l) = false.
  Proof.
    intros l x Hl H. destruct (in_rangesb x (zz2ww l)) eqn:C; [|reflexivity]. exfalso.
    destruct (zz_cases l x Hl C) as [p [Hp Hr]]. exact (H p Hp Hr).
  Qed.
  Lemma zz_contains : forall l a n b k, zz_ok l -> In (b, k) l -> b <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= b + k ->
    map_contains (zz2ww l) a n = true.
  Proof.
    intros l a n b k Hl Hin H0 H1. pose proof (proj1 (Forall_forall _ _) Hl (b, k) Hin) as [Hb Hk]. cbn [fst snd] in Hb, Hk.
    unfold map_contains. apply existsb_exists. exists (Z_to_bv 64 b, Z_to_bv 64 k). split.
    - unfold zz2ww. apply (in_map (fun p : Z * Z => (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p))) l (b, k)). exact Hin.
    - cbn [fst snd]. rewrite !u_of_Z by lia. apply andb_true_intro. split; apply Z.leb_le; lia.
  Qed.

  Lemma ak_maps_in : forall b k x, In (b, k) (PM_MAPS brk0z X) -> b <= bv_unsigned x < b + k -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros b k x Hin Hx. rewrite ak_maps. exact (zz_in _ _ _ _ zz_ok_maps Hin Hx). Qed.
  Lemma ak_maps_contains : forall b k a n, In (b, k) (PM_MAPS brk0z X) -> b <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= b + k ->
    map_contains (vm_maps VMM) a n = true.
  Proof. intros b k a n Hin H0 H1. rewrite ak_maps. exact (zz_contains _ _ _ _ _ zz_ok_maps Hin H0 H1). Qed.
  Lemma ak_maps_exact : forall b k, In (b, k) (PM_MAPS brk0z X) -> In (Z_to_bv 64 b, Z_to_bv 64 k) (vm_maps VMM).
  Proof. intros b k Hin. rewrite ak_maps. unfold zz2ww. apply (in_map (fun p : Z * Z => (Z_to_bv 64 (fst p), Z_to_bv 64 (snd p))) _ (b, k)). exact Hin. Qed.
  Lemma ak_zr_in : forall b k x, In (b, k) (PM_ZR sp0z X) -> b <= bv_unsigned x < b + k -> in_rangesb x (zz2ww (PM_ZR sp0z X)) = true.
  Proof. intros b k x Hin Hx. exact (zz_in _ _ _ _ zz_ok_zr Hin Hx). Qed.
  Lemma ak_lazy_in : forall b k x, In (b, k) (PM_LAZY sp0z X) -> b <= bv_unsigned x < b + k -> in_rangesb x (zz2ww (PM_LAZY sp0z X)) = true.
  Proof. intros b k x Hin Hx. exact (zz_in _ _ _ _ zz_ok_lazy Hin Hx). Qed.
  Lemma ak_S_in : forall b k x, In (b, k) (PM_S sp0z brk0z X) -> b <= bv_unsigned x < b + k -> in_rangesb x (zz2ww (PM_S sp0z brk0z X)) = true.
  Proof. intros b k x Hin Hx. exact (zz_in _ _ _ _ zz_ok_S Hin Hx). Qed.
  Lemma ak_noacc_cases : forall x, in_rangesb x (vm_noaccess VMM) = true ->
       (pm_meta_map brk0z X <= bv_unsigned x < pm_meta_map brk0z X + 4096)
    \/ (ps_b08 X <= bv_unsigned x < ps_b08 X + 0x800000)
    \/ (ps_b06 X <= bv_unsigned x < pm_region_info X)
    \/ (pm_region_info X + 4096 <= bv_unsigned x < ps_b06 X + 0x2000011000)
    \/ (0x8fff7000 <= bv_unsigned x < 0x2008fff7000).
  Proof.
    intros x Hx. rewrite ak_noacc in Hx. destruct (zz_cases _ _ zz_ok_noacc Hx) as [p [Hp Hr]].
    unfold PM_NOACC, PM_REM in Hp. rewrite !in_app_iff in Hp. cbn [In] in Hp.
    destruct Hp as [[<-|[<-|[<-|[]]]]|[Hp|[<-|[]]]]; cbn [fst snd] in Hr; try lia.
    destruct (pm_region_info X + 4096 <? ps_b06 X + 0x2000011000) eqn:C; cbn [In] in Hp; [|tauto].
    destruct Hp as [<-|[]]. cbn [fst snd] in Hr. lia.
  Qed.

  Lemma al_AE : 0x7fff8000 + page_down sp0z / 8 <= 0x10007fff8000.
  Proof.
    pose proof lz_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VSP). pose proof pd_facts as (PD1 & PD2 & PD3).
    assert (page_down sp0z / 8 <= 0x800000000000 / 8) by (apply Z.div_le_mono; lia). lia.
  Qed.

  Lemma ak3_T   : forall x, ps_b09 X <= bv_unsigned x < ps_b09 X + 4096 -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. apply (ak_maps_in (ps_b09 X) 0x1000); [unfold PM_MAPS; cbn [In]; tauto | lia]. Qed.
  Lemma ak3_CTX : forall x, ps_b10 X <= bv_unsigned x < ps_b10 X + 0x10000 -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. apply (ak_maps_in (ps_b10 X) 0x10000); [unfold PM_MAPS; cbn [In]; tauto | lia]. Qed.
  Lemma ak3_space : forall x, ps_b06 X <= bv_unsigned x < ps_b06 X + 0x2000011000 -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. apply (ak_maps_in (ps_b06 X) 0x2000011000); [unfold PM_MAPS; cbn [In]; tauto | lia]. Qed.
  Lemma ak3_SB : forall x, pm_space_beg X <= bv_unsigned x < pm_space_beg X + 2 ^ 37 + 4096 -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. pose proof al_SB as SB. apply ak3_space. lia. Qed.
  Lemma ak3_PA : forall x, ps_b08 X <= bv_unsigned x < ps_b08 X + 0x800000 -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. apply (ak_maps_in (ps_b08 X) 0x800000); [unfold PM_MAPS; cbn [In]; tauto | lia]. Qed.
  Lemma ak3_FSB : forall x, ps_b16 X <= bv_unsigned x < ps_b16 X + 0xb09000 -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. apply (ak_maps_in (ps_b16 X) 0xb09000); [unfold PM_MAPS; cbn [In]; tauto | lia]. Qed.
  Lemma ak3_D : forall x, ps_b12 X <= bv_unsigned x < ps_b12 X + 4096 -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. apply (ak_maps_in (ps_b12 X) 0x1000); [unfold PM_MAPS; cbn [In]; tauto | lia]. Qed.

  Lemma ak8a : forall x, 0x7fff7000 <= bv_unsigned x < 0x10007fff8000 -> in_rangesb x (vm_maps VMM) = true.
  Proof.
    intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) 0x8fff7000); [| destruct (Z_lt_le_dec (bv_unsigned x) 0x2008fff7000)].
    - apply (ak_maps_in 0x7fff7000 0x10000000); [unfold PM_MAPS; cbn [In]; tauto | lia].
    - apply (ak_maps_in 0x8fff7000 0x20000000000); [unfold PM_MAPS; cbn [In]; tauto | lia].
    - apply (ak_maps_in 0x2008fff7000 0xdfff0001000); [unfold PM_MAPS; cbn [In]; tauto | lia].
  Qed.

  Lemma ak4_space : forall a n, ps_b06 X <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= ps_b06 X + 0x2000011000 -> map_contains (vm_maps VMM) a n = true.
  Proof. intros a n H0 H1. apply (ak_maps_contains (ps_b06 X) 0x2000011000); [unfold PM_MAPS; cbn [In]; tauto | lia | lia]. Qed.
  Lemma ak4_SB : forall a n, pm_space_beg X <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= pm_space_beg X + 2 ^ 37 + 4096 -> map_contains (vm_maps VMM) a n = true.
  Proof. intros a n H0 H1. pose proof al_SB as SB. apply ak4_space; lia. Qed.
  Lemma ak4_PA : forall a n, ps_b08 X <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= ps_b08 X + 0x800000 -> map_contains (vm_maps VMM) a n = true.
  Proof. intros a n H0 H1. apply (ak_maps_contains (ps_b08 X) 0x800000); [unfold PM_MAPS; cbn [In]; tauto | lia | lia]. Qed.
  Lemma ak4_hish : forall a n, 0x2008fff7000 <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= 0x10007fff8000 -> map_contains (vm_maps VMM) a n = true.
  Proof. intros a n H0 H1. apply (ak_maps_contains 0x2008fff7000 0xdfff0001000); [unfold PM_MAPS; cbn [In]; tauto | lia | lia]. Qed.
  Lemma ak4_losh : forall a n, 0x7fff7000 <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= 0x8fff7000 -> map_contains (vm_maps VMM) a n = true.
  Proof. intros a n H0 H1. apply (ak_maps_contains 0x7fff7000 0x10000000); [unfold PM_MAPS; cbn [In]; tauto | lia | lia]. Qed.

  Lemma ak5_space : forall x, ps_b06 X <= bv_unsigned x < ps_b06 X + 0x2000011000 -> in_rangesb x (zz2ww (PM_ZR sp0z X)) = false.
  Proof.
    intros x Hx. pose proof al_SB as SB. pose proof al_R6 as (G1 & G2 & G3 & G4 & G5). cbn [fst snd] in G1, G2, G3, G4, G5.
    pose proof (kp_apart_ne 2 11 _ _ ltac:(lia) kp_b06 kp_b22) as AP. cbn [fst snd] in AP.
    apply (zz_out _ _ zz_ok_zr). intros p Hp. unfold PM_ZR in Hp. cbn [In] in Hp.
    destruct Hp as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  Qed.
  Lemma ak5_PA : forall x, ps_b08 X <= bv_unsigned x < ps_b08 X + 0x800000 -> in_rangesb x (zz2ww (PM_ZR sp0z X)) = false.
  Proof.
    intros x Hx. pose proof al_PA as (G1 & G2 & G3 & G4 & G5). cbn [fst snd] in G1, G2, G3, G4, G5.
    pose proof (kp_apart_ne 3 11 _ _ ltac:(lia) kp_b08 kp_b22) as AP. cbn [fst snd] in AP.
    apply (zz_out _ _ zz_ok_zr). intros p Hp. unfold PM_ZR in Hp. cbn [In] in Hp.
    destruct Hp as [<-|[<-|[<-|[]]]]; cbn [fst snd]; lia.
  Qed.
  Lemma ak5_hish : forall x, 0x2008fff7000 <= bv_unsigned x < 0x10007fff8000 ->
    in_rangesb x (zz2ww (PM_ZR sp0z X)) = true /\ in_rangesb x (zz2ww (PM_LAZY sp0z X)) = true.
  Proof.
    intros x Hx. split.
    - apply (ak_zr_in 0x2008fff7000 0xdfff0001000); [unfold PM_ZR; cbn [In]; tauto | lia].
    - apply (ak_lazy_in 0x2008fff7000 0xdfff0001000); [unfold PM_LAZY; rewrite !in_app_iff; cbn [In]; tauto | lia].
  Qed.
  Lemma ak8c : forall x, 0x7fff7000 <= bv_unsigned x < 0x8fff7000 ->
    in_rangesb x (zz2ww (PM_ZR sp0z X)) = true /\ in_rangesb x (zz2ww (PM_LAZY sp0z X)) = true.
  Proof.
    intros x Hx. split.
    - apply (ak_zr_in 0x7fff7000 0x10000000); [unfold PM_ZR; cbn [In]; tauto | lia].
    - apply (ak_lazy_in 0x7fff7000 0x10000000); [unfold PM_LAZY; rewrite !in_app_iff; cbn [In]; tauto | lia].
  Qed.

  Lemma ak_sh_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> sh aceil + 4096 <= 0x10007fff8000 /\ sh BsShadow.AHI_LO = 0x2008fff7000.
  Proof.
    intros HCEIL Hh'. pose proof (al_ceil HCEIL Hh') as AC. pose proof al_AE as AE4. pose proof pd_facts as (PD1 & PD2 & PD3).
    unfold sh. rewrite AC. unfold BsShadow.AHI_LO, ASHADOW_BASE. split; [| reflexivity].
    replace (page_down sp0z - 8388608) with (page_down sp0z + (-1048576) * 8) by lia. rewrite Z.div_add by lia. lia.
  Qed.
  Lemma ak3_hish : forall x, sh BsShadow.AHI_LO <= bv_unsigned x < BsShadow.AHI_LO -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. unfold sh, BsShadow.AHI_LO, ASHADOW_BASE in Hx. apply ak8a. lia. Qed.
  Lemma ak4_hish_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    forall a n, sh BsShadow.AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil -> map_contains (vm_maps VMM) a n = true.
  Proof.
    intros HCEIL Hh' a n H0 H1 H2. pose proof (ak_sh_ceil HCEIL Hh') as [S1 S2].
    rewrite S2 in H0. apply ak4_hish; lia.
  Qed.
  Lemma ak5_hish_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    forall x, sh BsShadow.AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (zz2ww (PM_ZR sp0z X)) = true /\ in_rangesb x (zz2ww (PM_LAZY sp0z X)) = true.
  Proof. intros HCEIL Hh' x Hx. pose proof (ak_sh_ceil HCEIL Hh') as [S1 S2]. rewrite S2 in Hx. apply ak5_hish. lia. Qed.
  Lemma ak8a_sh : forall x, BsShadow.ALOWSH_LO <= bv_unsigned x < BsShadow.AHI_LO -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. unfold BsShadow.AHI_LO, BsShadow.ALOWSH_LO in Hx. apply ak8a. lia. Qed.
  Lemma ak8b_sh : forall a n, sh BSegs.AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh BsShadow.ALOWSH_LO -> map_contains (vm_maps VMM) a n = true.
  Proof. intros a n H0 H1 H2. unfold sh, BSegs.AIMG_TOP, BsShadow.ALOWSH_LO, ASHADOW_BASE in *. apply ak4_losh; lia. Qed.
  Lemma ak8c_sh : forall x, sh BSegs.AIMG_TOP <= bv_unsigned x < sh BsShadow.ALOWSH_LO ->
    in_rangesb x (zz2ww (PM_ZR sp0z X)) = true /\ in_rangesb x (zz2ww (PM_LAZY sp0z X)) = true.
  Proof. intros x Hx. unfold sh, BSegs.AIMG_TOP, BsShadow.ALOWSH_LO, ASHADOW_BASE in Hx. apply ak8c. lia. Qed.

  Lemma ak_budget : eager_used model <= 16519168 /\ vm_limit VMM = target_alloc_limit /\ pages_total (zz2ww (PM_S sp0z brk0z X)) <= PM_S_PAGES /\ PM_S_PAGES = 68900.
  Proof. split; [exact ak_eager|]. split; [exact ak_limit|]. split; [exact (BsMainLazy.pages_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) | reflexivity]. Qed.
End AT_MAIN.
