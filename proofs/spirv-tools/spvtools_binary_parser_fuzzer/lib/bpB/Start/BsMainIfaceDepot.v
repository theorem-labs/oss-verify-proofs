(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BArr BellsX BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 BsDepotInv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsPlanImagesHex BsMainIfaceDepotScan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BxSymExec3Sound BxSymExec3B BothAcct BothPlanCore BothPlan BothPlanSound BothPlanSoundSums BothInit BothHexScan BsImages BsPlanImages BsHSTab BsStartupHSF BsMainVM BsMainState BsMainFacts BsMainLazyChk BsMainLazy BsMainCells BsMainIface BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsMainSyms.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition pm_trace (sp0z : Z) : list Z := if pm_short sp0z then [0xa02a0] else [0xa02a0; 0xa15f0].
Definition pm_trace_hash (sp0z : Z) : Z := if pm_short sp0z then 0x6e9441911e99d6a6 else 0x82a065bf5a85d1af.
Definition pm_nframes (sp0z : Z) : Z := if pm_short sp0z then 2 else 3.
Definition pm_tab_slot (sp0z : Z) : Z := if pm_short sp0z then 5147056 else 4093396.

Definition depot0 (sp0z : Z) (X : pm_syms) : depot :=
  mkDepot 1 (pm_nframes sp0z) (fun _ => pm_trace_hash sp0z)
          (fun b => if b =? bucket (pm_trace_hash sp0z) then [1] else []) (ps_b21 X) (ps_b22 X).

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
  Ltac cszl := rewrite ?length_cellsZ in * by (cbn; tauto); csz.

  Lemma kp_b21f : 7241728 <= ps_b21 X /\ ps_b21 X + 0x100000 <= page_down sp0z - 8388608 /\ ps_b21 X mod 4096 = 0.
  Proof. pose proof (kp_facts _ _ kp_b21) as (A & B & C & D & _). cbn [fst snd] in A, B, C, D. lia. Qed.
  Lemma kp_b22f : 7241728 <= ps_b22 X /\ ps_b22 X + 0x800000 <= page_down sp0z - 8388608 /\ ps_b22 X mod 4096 = 0.
  Proof. pose proof (kp_facts _ _ kp_b22) as (A & B & C & D & _). cbn [fst snd] in A, B, C, D. lia. Qed.

  Lemma img_cells_w : forall (u : bool) A cs, pm_short sp0z = u ->
    cells_wfb cs = true -> 0x17e000 <= A -> A + Z.of_nat (cells_size cs) <= 0x6e8000 ->
    bytes_check_w (WS (Some u) None) (CAbs, A) (cellsZ cs) = true -> rw_cells asegs VM A cs.
  Proof.
    intros u A cs U WF H1 H2 HB. pose proof (cells_wfb_sound cs WF) as WF'.
    apply rw_cells_img; [exact WF' | lia | lia |]. rewrite <- map_b8_cellsZ.
    apply (bytes_main (WS (Some u) None) (CAbs, A) (cellsZ cs) HB (world_uw _ U)); pmc_simpl; rewrite ?(length_cellsZ cs WF'); [lia | lia | apply vr_img; lia].
  Qed.

  Lemma obj_cells_w : forall (u : bool) a cs lo hi, pm_short sp0z = u -> bytes_check_w (WS (Some u) None) a (cellsZ cs) = true -> cells_wfb cs = true ->
    vrange lo hi -> lo <= CXV a -> CXV a + Z.of_nat (cells_size cs) <= hi -> 0x6e8000 <= lo -> hi <= 2 ^ 64 -> rw_cells asegs VM (CXV a) cs.
  Proof.
    intros u a cs lo hi U Hc WF VR H0 H1 H2 H3. apply cells_wfb_sound in WF. apply rw_cells_above; [exact WF | lia | lia |].
    rewrite <- map_b8_cellsZ. apply (bytes_main (WS (Some u) None) a (cellsZ cs) Hc (world_uw _ U)); rewrite ?(length_cellsZ cs WF); [lia | lia |].
    eapply vr_sub; [exact VR | lia | lia].
  Qed.

  Lemma dp_nui : rw_cells asegs VM 6762264 [C4 (wz 1)].
  Proof. exact (img_cells_main 6762264 [C4 (wz 1)] ltac:(vm_compute; reflexivity)). Qed.
  Lemma dp_map1 : rw_cells asegs VM 6762280 [C8 (wz (ps_b21 X))].
  Proof. replace (ps_b21 X) with (CXV (CB21, 0)) by (pmc_simpl; lia). apply (img_word_main 6762280 (CB21, 0) ltac:(vm_compute; reflexivity)); lia. Qed.

  Lemma seg_rom_bss_tab : forall z, 2567960 <= z < 6762264 -> BPropExec.seg_rom ASEGS (wa z) = Some (b8 0).
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
    symmetry. eapply (BothHexTree.segment_byte_at_zero_pt _ _ _ _ BsMainIfaceDepotScan.tab_zero_scan); [rewrite asan_len3; cbn; lia | lia].
  Qed.

  Lemma dp_tab_pristine : forall lo hi z, img_check lo hi = true -> lo <= z < hi -> 2567960 <= lo -> hi <= 6762264 -> mrd asegs VM (wa z) = Some (b8 0).
  Proof.
    intros lo hi z Hc Hz H1 H2. pose proof (pmc_img _ _ _ _ _ _ MC lo hi Hc z Hz) as HN. fold (wa z) in HN.
    unfold mrd. rewrite (vm_img z ltac:(lia)), HN, seg_rom_lib, asegs_ASEGS. apply seg_rom_bss_tab. lia.
  Qed.
  Lemma dp_tab_zero4 : forall A, (2567960 <= A /\ A + 4 <= 4093396) \/ (4093400 <= A /\ A + 4 <= 5147056) \/ (5147060 <= A /\ A + 4 <= 6762264) ->
    rw_cells asegs VM A [C4 (wz 0)].
  Proof.
    intros A HA. apply rw_cells_img; [cbn; tauto | lia | csz; lia |].
    apply bytes_at_of_nth; [lia | change (length (cells_bytes [C4 (wz 0)])) with 4%nat; lia |]. intros i Hi.
    change (length (cells_bytes [C4 (wz 0)])) with 4%nat in Hi.
    assert (Hb : nth_error (cells_bytes [C4 (wz 0)]) i = Some (b8 0)) by (destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]).
    rewrite Hb.
    destruct HA as [HA|[HA|HA]].
    - apply (dp_tab_pristine 2567960 4093396); [vm_compute; reflexivity | lia | lia | lia].
    - apply (dp_tab_pristine 4093400 5147056); [vm_compute; reflexivity | lia | lia | lia].
    - apply (dp_tab_pristine 5147060 6762264); [vm_compute; reflexivity | lia | lia | lia].
  Qed.

  Lemma dp_tab_slots : rw_cells asegs VM 5147056 [C4 (wz (if pm_short sp0z then 1 else 0))] /\ rw_cells asegs VM 4093396 [C4 (wz (if pm_short sp0z then 0 else 1))].
  Proof.
    destruct (pm_short sp0z) eqn:U; split.
    - exact (img_cells_w true 5147056 [C4 (wz 1)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - exact (img_cells_w true 4093396 [C4 (wz 0)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - exact (img_cells_w false 5147056 [C4 (wz 0)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - exact (img_cells_w false 4093396 [C4 (wz 1)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
  Qed.

  Lemma buckets : bucket 0x6e9441911e99d6a6 = 644774 /\ bucket 0x82a065bf5a85d1af = 381359.
  Proof. split; reflexivity. Qed.
  Lemma dp_tab : forall b, 0 <= b < 2 ^ 20 -> rw_cells asegs VM (2567960 + 4 * b) [C4 (wz (hd 0 (d_chain (depot0 sp0z X) b)))].
  Proof.
    intros b Hb. pose proof dp_tab_slots as [S1 S2]. pose proof buckets as [BS BL]. cbn [depot0 d_chain]. unfold pm_trace_hash in *.
    destruct (pm_short sp0z); [rewrite BS | rewrite BL].
    - destruct (Z.eqb_spec b 644774) as [->|N1]; cbn [hd]; [change (2567960 + 4 * 644774) with 5147056; exact S1|].
      destruct (Z.eq_dec b 381359) as [->|N2]; [change (2567960 + 4 * 381359) with 4093396; exact S2|].
      apply dp_tab_zero4. lia.
    - destruct (Z.eqb_spec b 381359) as [->|N1]; cbn [hd]; [change (2567960 + 4 * 381359) with 4093396; exact S2|].
      destruct (Z.eq_dec b 644774) as [->|N2]; [change (2567960 + 4 * 644774) with 5147056; exact S1|].
      apply dp_tab_zero4. lia.
  Qed.

  Lemma dp_node1 : rw_cells asegs VM (ps_b21 X + 16) [C8 (wz (pm_trace_hash sp0z)); C4 (wz 0)] /\ rw_cells asegs VM (ps_b21 X + 28) [C4 (wz 1)].
  Proof.
    pose proof kp_b21f as (B1 & B2 & _). pose proof pd_facts as PD. unfold pm_trace_hash. destruct (pm_short sp0z) eqn:U; split.
    - pose proof (obj_cells_w true (CB21, 16) [C8 (wz 0x6e9441911e99d6a6); C4 (wz 0)] _ _ U ltac:(vm_compute; reflexivity) eq_refl vr_b21) as W.
      revert W. pmc_simpl. csz. intros W. apply W; lia.
    - pose proof (obj_cells_w true (CB21, 28) [C4 (wz 1)] _ _ U ltac:(vm_compute; reflexivity) eq_refl vr_b21) as W. revert W. pmc_simpl. csz. intros W. apply W; lia.
    - pose proof (obj_cells_w false (CB21, 16) [C8 (wz 0x82a065bf5a85d1af); C4 (wz 0)] _ _ U ltac:(vm_compute; reflexivity) eq_refl vr_b21) as W.
      revert W. pmc_simpl. csz. intros W. apply W; lia.
    - pose proof (obj_cells_w false (CB21, 28) [C4 (wz 1)] _ _ U ltac:(vm_compute; reflexivity) eq_refl vr_b21) as W. revert W. pmc_simpl. csz. intros W. apply W; lia.
  Qed.
  Lemma dp_nodes_zero_hi : forall z, ps_b21 X + 32 <= z < ps_b21 X + 0x100000 -> VM (wa z) = Some (b8 0).
  Proof.
    pose proof kp_b21f as (B1 & B2 & _). pose proof pd_facts as PD.
    pose proof (obj_zero_main (CB21, 32) (0x100000 - 32) _ _ ltac:(vm_compute; reflexivity) (fun z Hz => proj1 (vr_b21 z Hz))) as W. revert W. pmc_simpl. intros W z Hz. apply W; lia.
  Qed.
  Lemma dp_free : forall id, 1 < id < 65536 -> exists j1 j2 j3, rw_cells asegs VM (ps_b21 X + 16 * id) [C8 j1; C4 j2; C4 j3].
  Proof.
    intros id Hid. pose proof kp_b21f as (B1 & B2 & _). pose proof pd_facts as PD.
    exists (wz 0), (wz 0), (wz 0). apply rw_cells_above; [cbn; tauto | lia | csz; lia |].
    apply bytes_at_of_nth; [lia | csz; lia |]. intros i Hi.
    replace (cells_bytes [C8 (wz 0); C4 (wz 0); C4 (wz 0)]) with (repeat (b8 0) 16) in Hi |- * by reflexivity.
    rewrite repeat_length in Hi. rewrite (nth_error_repeat (b8 0) Hi). unfold mrd. rewrite (dp_nodes_zero_hi (ps_b21 X + 16 * id + Z.of_nat i) ltac:(lia)). reflexivity.
  Qed.

  Lemma dp_store_hdr : rw_cells asegs VM 2502408 [C8 (wz (pm_nframes sp0z))] /\ rw_cells asegs VM 2502424 [C8 (wz (ps_b22 X))]
                       /\ rw_cells asegs VM 2502432 [C4 (wz (pm_nframes sp0z))].
  Proof.
    unfold pm_nframes. split; [|split].
    - destruct (pm_short sp0z) eqn:U.
      + exact (img_cells_w true 2502408 [C8 (wz 2)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
      + exact (img_cells_w false 2502408 [C8 (wz 3)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - replace (ps_b22 X) with (CXV (CB22, 0)) by (pmc_simpl; lia). apply (img_word_main 2502424 (CB22, 0) ltac:(vm_compute; reflexivity)); lia.
    - destruct (pm_short sp0z) eqn:U.
      + exact (img_cells_w true 2502432 [C4 (wz 2)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
      + exact (img_cells_w false 2502432 [C4 (wz 3)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
  Qed.

  Lemma dp_store_zero : forall z, ps_b22 X + 8 * pm_nframes sp0z <= z < ps_b22 X + 0x40000 -> VM (wa z) = Some (b8 0).
  Proof.
    pose proof kp_b22f as (B1 & B2 & _). pose proof pd_facts as PD. unfold pm_nframes.
    destruct (pm_short sp0z) eqn:U; intros z Hz.
    - apply (zero_main (WS (Some true) None) (CB22, 16) (0x40000 - 16) ltac:(vm_compute; reflexivity) (world_uw _ U) ltac:(lia)); [|revert Hz; pmc_simpl; lia].
      intros y Hy. apply vm_b22. revert Hy. pmc_simpl. lia.
    - apply (zero_main (WS (Some false) None) (CB22, 24) (0x40000 - 24) ltac:(vm_compute; reflexivity) (world_uw _ U) ltac:(lia)); [|revert Hz; pmc_simpl; lia].
      intros y Hy. apply vm_b22. revert Hy. pmc_simpl. lia.
  Qed.
  Lemma dp_space : exists junk, u8arr asegs VM (ps_b22 X + 8 * pm_nframes sp0z) junk /\ Z.of_nat (length junk) = 8 * (32768 - pm_nframes sp0z).
  Proof.
    pose proof kp_b22f as (B1 & B2 & _). pose proof pd_facts as PD.
    assert (NF : 2 <= pm_nframes sp0z <= 3) by (unfold pm_nframes; destruct (pm_short sp0z); lia).
    exists (repeat (b8 0) (Z.to_nat (8 * (32768 - pm_nframes sp0z)))). split; [| rewrite repeat_length; lia].
    apply u8arr_constZ; [lia | lia | lia |]. intros z Hz. apply dp_store_zero. lia.
  Qed.

  Theorem depot_main : DEPOT asegs (depot0 sp0z X) VM.
  Proof.
    pose proof kp_b21f as (B1 & B2 & _). pose proof kp_b22f as (C1 & C2 & _). pose proof pd_facts as PD.
    pose proof (kp_apart 10 11 _ _ ltac:(lia) kp_b21 kp_b22) as A. cbn [fst snd] in A.
    assert (NF : 2 <= pm_nframes sp0z <= 3) by (unfold pm_nframes; destruct (pm_short sp0z); lia).
    assert (HH : 0 <= pm_trace_hash sp0z < 2 ^ 64) by (unfold pm_trace_hash; destruct (pm_short sp0z); lia).
    pose proof (bucket_range (pm_trace_hash sp0z)) as BR.
    split.
    -   constructor; cbn [depot0 d_ids d_frames d_hash d_chain d_nb d_sb]; unfold BSegs.AIMG_TOP.
      + lia.
      + lia.
      + intros id Hid. lia.
      + intros id Hid. rewrite Z.eqb_refl. left. lia.
      + intros b id Hin. destruct (Z.eqb_spec b (bucket (pm_trace_hash sp0z))) as [->|NE]; [|destruct Hin]. destruct Hin as [<-|[]]. split; [lia | reflexivity].
      + intros b. destruct (b =? bucket (pm_trace_hash sp0z)); [repeat constructor; cbn; tauto | constructor].
      + lia.
      + lia.
      + lia.
    -   pose proof dp_node1 as [N1 N2]. pose proof dp_store_hdr as (S1 & S2 & S3).
      constructor; cbn [depot0 d_ids d_frames d_hash d_chain d_nb d_sb].
      + exact dp_tab.
      + exact dp_nui.
      + exact dp_map1.
      + intros id Hid. replace id with 1 by lia. rewrite Z.eqb_refl. cbn [link_of Z.eqb hd]. replace (ps_b21 X + 16 * 1) with (ps_b21 X + 16) by lia. exact N1.
      + intros id Hid. replace id with 1 by lia. exists (wz 1). replace (ps_b21 X + 16 * 1 + 12) with (ps_b21 X + 28) by lia. exact N2.
      + intros id Hid. apply dp_free. lia.
      + exact S1.
      + exact S2.
      + exact S3.
      + exact dp_space.
  Qed.
End AT_MAIN.
