(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up invariant at the run's mmap base; the argument lemmas restated for the revised entry block, with the strings at its top, under the launch conjunct and with 10 bytes of room above an argument string, after the same lemmas of boost-beast/http_request's As/AsMainIfaceArgs.v). *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BCells BStep BLFrame BArr BellsX BacX.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsStack0 BsPrintfFirst BsDrvDefs BsMainPre.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BCatExec BRefLayout BArgvEnv BFileSim BMuslStrlen.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BxSymExec3Sound BxSymExec3B BothAcct BothPlanCore BothPlan BothPlanSound BothPlanSoundSums BothInit BothHexScan BsImages BsPlanImages BsHSTab BsStartupHSF BsMainVM BsMainState BsMainFacts BsMainLazyChk BsMainLazy BsMainCells BsMainIface BazyRestrict BazySR.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsMainSyms.
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
  (* LPS #38: [AsanInit]/[BothInit] now take the mmap base; IMPLICIT so every caller
     infers it by unification from the [cs_ok] hypothesis it already passes. *)
  Context {mbase : word}.
  Hypothesis HC : cs_ok ASEGS ASAN_H BothInit.LIMIT (SINV0 APH AENTRY sp0 rdraw brk0 mbase inp)
                        (argH0 sp0 rdraw inp) (in_fs inp) E ch R FULL model.
  (* [Run.valid_entry]'s launch conjunct at the run's mmap base: it pins the [arch_align_stack] pad and so
     the string area's place at the top of the entry block (BsMainState.P_mainL carries it to main) *)
  Hypothesis Vlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mbase rdraw) inp.
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
  #[local] Notation args_block := (BsMainCells.args_block sp0 brk0 rdraw inp ch E R FULL model Vsp Vav Vev Vfit HC Vlau) (only parsing).
  #[local] Notation Mr_some := (BsMainCells.Mr_some sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_vis_none := (BsMainCells.Mr_vis_none sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation rdn_Mr_full := (BsMainCells.rdn_Mr_full sp0 brk0 rdraw inp ch E FULL model) (only parsing).

  #[local] Notation MR := (Mr ASAN_H (argH0 sp0 rdraw inp) E ch model FULL).
  #[local] Notation HID := (hid ASAN_H (argH0 sp0 rdraw inp) E ch model).
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation envc := (Z.of_nat (length (in_envp inp))).
  (* The entry block is [entry_stack_image inp mbase APH ENTW sp0 rdraw]: it runs from sp0 to the stack VMA's end
     [UTOP]; its head [CHD] (sp0 to the top of the AT_RANDOM bytes), the [arch_align_stack] pad [PAD], the string
     bytes [LSTR] (argv, envp, the exec name, each with its NUL) and argv[0]'s address [STRB]
     (StackLayout.build_stack_bytes, BCatExec.cat_string_off) *)
  #[local] Notation UTOP := (bv_unsigned (ed_top rdraw)).
  #[local] Notation CHD := (Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  #[local] Notation LSTR := (Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  #[local] Notation PAD := (Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))).
  #[local] Notation STRB := (sp0z + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))).
  #[local] Notation ENTW := (Z_to_bv 64 (Z.of_N AENTRY)).
  #[local] Notation BSB := (entry_stack_image inp mbase APH ENTW sp0 rdraw).
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.

  Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
  Definition args_check : bool :=
    all_holes (fun g cls ch =>
      let bc := mkbc (kn ch) in
      has_fact (kn ch) (KWord (SA e_sp0 8) 8 e_str0) && has_fact (kn ch) (kw_argv1 e_argv1w) && has_fact (kn ch) atr_entry
      && isSome (lin_ofxB bc e_sp0) && isSome (lin_ofxB bc e_str0) && isSome (lin_ofxB bc e_str1) && isSome (lin_ofxB bc (fst e_atrb))).
  Lemma args_check_ok : args_check = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma cs_v3 : vE E 3 = Z.of_nat (length (nth 0 argv [])).
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 3%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z.
    pose proof Vav as (Hl & _ & Hs & _ & _). assert (Hin : In (nth 0 argv []) argv) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) Hs _ Hin) as L. cbv beta in L. lia.
  Qed.
  (* The block's arithmetic under the launch conjunct: [Run.valid_launch_sp] puts sp0 between [launch_sp_lo] and
     [launch_sp_hi], so the pad does not clamp and is at most 4095 + 15; argv[0] sits [LSTR + 8] below the stack
     VMA's end ([StackLayout.string_base_addr]); [Run.valid_stack_top_va] keeps that end at or below STACK_TOP
     ([BothInit.ai_entry_page_top_within_window]).  The steps of [BothInit.pad_bounds_Z]. *)
  Lemma launch_lay : 0 <= PAD <= 4110 /\ STRB + LSTR + 8 = UTOP /\ UTOP <= 0x800000000000.
  Proof.
    pose proof (ai_entry_page_top_within_window Sv48 inp mbase sp0 brk0 rdraw Vlau) as HT.
    unfold entry_page_top, va_stack_top, sp_window_hi in HT.
    pose proof Vlau as Hl. cbn [entry_launch_ok_va] in Hl. destruct Hl as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
    pose proof (Z.mod_pos_bound (UTOP - 8 - LSTR) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (UTOP - 8 - LSTR - 4095) 16 ltac:(lia)).
    unfold cat_string_off, block_pad_len. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    split; [lia|]. split; lia.
  Qed.

  (* vals0's indices 11 and 12 (BothInit.vals0): the [STACK_ROUND] gap in words and CONFIG_RSEQ *)
  Lemma cs_v11 : vE E 11 = Z.of_nat (block_items argv envp mod 2).
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 11%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z.
    pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)). lia.
  Qed.
  Lemma cs_v12 : vE E 12 = rseq_z (kb_rseq (in_kernel inp)).
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 12%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z. pose proof (rseq_z_range (kb_rseq (in_kernel inp))). lia.
  Qed.
  (* [StackLayout.block_head_size]: 8 * (argc + envc + 3) + the auxv + the [STACK_ROUND] gap + 16 (BothInit.chead_eq) *)
  Lemma chd_eq : CHD = 8 * argc + 8 * envc + 472 + 32 * rseq_z (kb_rseq (in_kernel inp)) + 8 * Z.of_nat (block_items argv envp mod 2).
  Proof.
    pose proof (auxv_size_rseq (kb_rseq (in_kernel inp))) as HA.
    unfold block_head_size, block_items. cbv zeta. lia.
  Qed.

  (* V_W (vals0 index 4) is the [arch_align_stack] pad between the AT_RANDOM bytes and argv[0] *)
  Lemma W_facts : 0 <= vE E 4 <= 4110 /\ STRB = sp0z + CHD + vE E 4.
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. pose proof launch_lay as (HP & _).
    unfold vE. rewrite (HE 4%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. rewrite u_of_Z by lia.
    unfold cat_string_off. rewrite Nat2Z.inj_add. split; lia.
  Qed.

  Lemma no_wrap : forall e, isSome (lin_ofxB (mkbc (kn ch)) e) = true -> uE E e = lden E (lin_of e).
  Proof.
    intros e H. destruct (lin_ofxB (mkbc (kn ch)) e) as [l|] eqn:L; [|discriminate].
    rewrite lin_ofxB_eqf in L. pose proof (lin_ofx_sound _ _ _ _ KNF _ _ L) as S.
    unfold lin_ofx in L. destruct (lin_nowrapR (kn ch) e); [|discriminate]. injection L as <-. exact S.
  Qed.

  Lemma lin_e_sp0 : lin_of e_sp0 = (0, [(32768, EVar 0); (4096, EVar 6); (16, EVar 10)]).
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_str0 : lin_of e_str0 = (472, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (1, EVar 4); (4096, EVar 6); (16, EVar 10); (8, EVar 11); (32, EVar 12)]).
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_str1 : lin_of e_str1 = (473, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (1, EVar 3); (1, EVar 4); (4096, EVar 6); (16, EVar 10); (8, EVar 11); (32, EVar 12)]).
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_atrb : lin_of (fst e_atrb) = (0, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (4096, EVar 6); (16, EVar 10); (8, EVar 11); (32, EVar 12)]) /\ snd e_atrb = 456.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma arg_facts :
    has_fact (kn ch) (KWord (SA e_sp0 8) 8 e_str0) = true /\ has_fact (kn ch) (kw_argv1 e_argv1w) = true /\ has_fact (kn ch) atr_entry = true
    /\ uE E e_sp0 = sp0z /\ uE E e_str0 = STRB
    /\ uE E e_str1 = STRB + Z.of_nat (length (nth 0 argv [])) + 1
    /\ uE E (fst e_atrb) + snd e_atrb = sp0z + CHD - 16.
  Proof.
    pose proof args_check_ok as H0. unfold args_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply andb_prop in H as [H N4]. apply andb_prop in H as [H N3]. apply andb_prop in H as [H N2]. apply andb_prop in H as [H N1].
    apply andb_prop in H as [H F3]. apply andb_prop in H as [F1 F2].
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & SP & _ & _ & V1 & V2 & _).
    pose proof cs_v3 as V3. pose proof W_facts as (W1 & W2). pose proof cs_v11 as V11. pose proof cs_v12 as V12. pose proof chd_eq as CH.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
    rewrite (no_wrap _ N1), (no_wrap _ N2), (no_wrap _ N3), (no_wrap _ N4).
    pose proof lin_e_atrb as [LA SA]. rewrite lin_e_sp0, lin_e_str0, lin_e_str1, LA, SA.
    unfold lden. cbn [fst snd tden]. rewrite !uE_var. rewrite V1, V2, V3, V11, V12. repeat split; lia.
  Qed.

  (* The block runs from sp0 to [UTOP] (its length is [UTOP - sp0z], BPropExec.length_entry_stack_image_launch),
     with the strings at its top *)
  Lemma lay :
    8 * argc + 8 * envc + 200 <= UTOP - sp0z /\ UTOP <= 2 ^ 47 /\ 1 <= argc <= 1024 /\ 0 <= envc <= 256
    /\ 0x7fff80000000 <= sp0z <= 0x800000000000 /\ STRB + LSTR + 8 = UTOP.
  Proof.
    pose proof launch_lay as (HP & HS & HT).
    pose proof Vav as [[LA1 LA2] _]. pose proof Vev as [LE _]. pose proof Vsp as [V1 [V2 _]].
    unfold sp_window_lo, sp_window_hi in V1, V2.
    assert (HCH : 8 * argc + 8 * envc + 472 <= CHD).
    { pose proof chd_eq. pose proof (rseq_z_range (kb_rseq (in_kernel inp))). lia. }
    assert (HSO : STRB = sp0z + CHD + PAD) by (unfold cat_string_off; rewrite Nat2Z.inj_add; lia).
    pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp (in_execfn inp))).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
  Qed.

  (* The k-th argv pointer: argv[k] = argv[0] + the bytes of the strings before it (BCatExec.cat_argv_ptr_offset),
     argv[0] = sp0 + cat_string_off (BCatExec.cat_string_base_offset, launch conjunct) *)
  Lemma u_ptr : forall k, (k < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k) = STRB + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof.
    intros k Hk. pose proof lay as (_ & HT & _ & _ & VS & ST).
    pose proof (total_arg_bytes_firstn_le k argv) as TF. pose proof (length_flatten_strings argv) as LF.
    unfold launch_string_bytes in ST.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) argv envp (in_execfn inp) k Hk).
    rewrite (cat_string_base_offset Sv48 inp mbase sp0 brk0 rdraw Vlau).
    rewrite !word_add_nat_Z2bv.
    rewrite (u_of_Z (sp0z + _)) by lia.
    apply u_of_Z. lia.
  Qed.

  (* Above argv[k]'s NUL lie at least the exec name's NUL and the 8-byte top slot (StackLayout.launch_string_bytes
     counts [length execfn + 1]; BCatExec.total_arg_bytes_firstn_within): ten bytes from argv[k] + |argv[k]| stay in
     the block, where the old block's sixteen AT_RANDOM bytes above the strings gave 17 *)
  Lemma room : forall k, (k < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k) + Z.of_nat (length (nth k argv [])) + 10 <= UTOP.
  Proof.
    intros k Hk. pose proof lay as (_ & _ & _ & _ & _ & ST). rewrite (u_ptr k Hk).
    pose proof (total_arg_bytes_firstn_within argv k Hk) as TW. pose proof (length_flatten_strings argv) as LF.
    unfold launch_string_bytes in ST. lia.
  Qed.

  Lemma stack_to_mem_some : forall (x : Z), sp0z <= x < UTOP -> exists b, stack_to_mem sp0 BSB (wa x) = Some b.
  Proof.
    intros x Hx. pose proof lay as (_ & HT & _ & _ & VS & _).
    pose proof (length_entry_stack_image_launch Sv48 inp mbase APH ENTW sp0 brk0 rdraw Vlau) as HL.
    unfold stack_to_mem. cbv zeta. rewrite !(wa_unsigned x) by lia.
    replace (sp0z <=? x) with true by (symmetry; apply Z.leb_le; lia).
    replace (x - sp0z <? Z.of_nat (length BSB)) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (nth_error BSB (Z.to_nat (x - sp0z))) as [b|] eqn:Hn; [exists b; reflexivity|].
    apply nth_error_None in Hn. lia.
  Qed.

  (* The hidden half of the block is the whole string area [STRB, UTOP) (BothInit.argB0), which the invariant pins
     to the image at the run's mmap base ([args_block]) *)
  Lemma block_full : forall x : Z, STRB <= x < UTOP -> FULL (wa x) = stack_to_mem sp0 BSB (wa x).
  Proof.
    intros x Hx. pose proof lay as (_ & HT & _ & _ & VS & _).
    rewrite <- (wrap_above_sp inp mbase APH ENTW sp0 rdraw (wa x)) by (rewrite wa_unsigned by lia; lia).
    apply args_block. unfold argB0. cbv beta zeta. rewrite wa_unsigned by lia.
    unfold cat_string_off in Hx. rewrite Nat2Z.inj_add in Hx.
    apply orb_true_intro. right. apply andb_true_intro.
    split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* The sixteen AT_RANDOM bytes sit [CHD - 16] above sp0, below the pad and the strings *)
  Lemma atr_full : forall x : Z, sp0z + CHD - 16 <= x < sp0z + CHD -> exists b, FULL (wa x) = Some b.
  Proof.
    intros x Hx. pose proof arg_facts as (_ & _ & F3 & _ & _ & _ & UA).
    unfold has_fact in F3. apply existsb_exists in F3 as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. unfold atr_entry in KO. cbn [kentry_ok] in KO. destruct KO as (FL & LEN & BL).
    unfold elenZ in BL, LEN. fold (uE E (ELit 16)) in BL, LEN. rewrite (uE_lit' 16 ltac:(lia)) in BL, LEN.
    assert (ES : estart E (SA (fst e_atrb) (snd e_atrb)) = sp0z + CHD - 16).
    { unfold estart. cbn [a_base a_off]. fold (uE E (fst e_atrb)). exact UA. }
    specialize (BL (x - estart E (SA (fst e_atrb) (snd e_atrb))) ltac:(lia)).
    replace (estart E (SA (fst e_atrb) (snd e_atrb)) + (x - estart E (SA (fst e_atrb) (snd e_atrb)))) with x in BL by lia.
    eexists. apply Mr_some'. exact BL.
  Qed.

  (* The string area [STRB, UTOP) is all in the image, so every byte of it is present *)
  Lemma upper_vm_some : forall x : Z, STRB <= x < UTOP -> exists b, VM (wa x) = Some b.
  Proof.
    intros x Hx. pose proof lay as (_ & HT & _ & _ & VS & _). pose proof pd_facts as PD.
    rewrite (vm_stack x ltac:(lia)).
    rewrite (block_full x Hx). apply stack_to_mem_some. lia.
  Qed.

  Lemma rdn_some_of : forall m n (a : Z), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall x, a <= x < a + Z.of_nat n -> exists b, m (wa x) = Some b) -> exists bs, rdn ASEGS m (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros m n. induction n as [|n IH]; intros a Ha Hn H; [exists []; reflexivity|].
    cbn [rdn]. destruct (H a ltac:(lia)) as [b Hb]. unfold wa in Hb. rewrite Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply H; lia)) as [bs Hbs].
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    - rewrite Hbs. exists (b :: bs). reflexivity.
    - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : word)) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
  Qed.

  Lemma wa_word : forall x : word, wa (bv_unsigned x) = x.
  Proof. intros x. unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

  (* the read goes through the image at the run's mmap base ([block_full]), and the bound [p + |s| + 10 <= 2^47]
     is [room] with [UTOP <= 2^47] ([lay]) *)
  Lemma arg_string : forall k, (k < length argv)%nat -> astr_at VM sp0 (bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k)) (nth k argv []).
  Proof.
    intros k Hk. pose proof lay as (_ & HT & LA & LE & VS & ST). pose proof pd_facts as PD.
    pose proof (u_ptr k Hk) as UP. pose proof (room k Hk) as RM.
    pose proof (total_arg_bytes_firstn_le k argv) as TF.
    unfold astr_at. change AsanUbsan.M.loaded_segments with ASEGS.
    set (p := bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k)) in *.
    split; [lia|]. split; [lia|]. split.
    { pose proof Vav as (_ & _ & _ & Hn & _). apply (proj1 (Forall_forall _ _) Hn). apply nth_In. exact Hk. }
    split.
    - rewrite <- (read_argv_cstr_k Sv48 ASEGS inp mbase APH ENTW sp0 brk0 rdraw k Vlau Hk).
      replace (Z_to_bv 64 p) with (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k) by (subst p; symmetry; apply wa_word).
      apply rdn_ext; [fold p; lia|]. intros x Hx. fold p in Hx. rewrite <- (wa_word x).
      rewrite (vm_stack (bv_unsigned x) ltac:(pose proof (u64_range x); lia)). apply block_full. lia.
    - apply (rdn_some_of VM 8 (p + Z.of_nat (length (nth k argv [])))); [lia | lia |]. intros x Hx. apply upper_vm_some. lia.
  Qed.

  Lemma slot_main : forall (off : Z) (v : expr) (w : word),
    has_fact (kn ch) (KWord (SA e_sp0 off) 8 v) = true -> 0 <= off -> off + 8 <= 8 * argc + 16 -> edenot E v = w ->
    rdn ASEGS VM (Z_to_bv 64 (sp0z + off)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros off v w HF Ho1 Ho2 Hv. pose proof lay as (G & UF & LA & LE & VS & _). pose proof pd_facts as PD.
    pose proof arg_facts as (_ & _ & _ & USP & _).
    unfold has_fact in HF. apply existsb_exists in HF as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. cbn [kentry_ok] in KO. destruct KO as (_ & FL & RD).
    assert (Ha : adenot E (SA e_sp0 off) = Z_to_bv 64 (sp0z + off)).
    { apply bv_eq. rewrite (flat_u E _ _ FL). unfold estart. cbn [a_base a_off]. fold (uE E e_sp0). rewrite USP, u_of_Z; [reflexivity | lia]. }
    rewrite Ha, Hv in RD.
    assert (RF : rdn ASEGS FULL (Z_to_bv 64 (sp0z + off)) 8 = Some (word_to_le_bytes 8 w)).
    { apply (rdn_Mr_full _ _ _ RD). intros i Hi. rewrite u_of_Z by lia. apply hid_stack. lia. }
    rewrite <- RF. apply rdn_ext; [rewrite u_of_Z by lia; lia|]. intros x Hx. rewrite u_of_Z in Hx by lia.
    rewrite <- (wa_word x). apply vm_stack. lia.
  Qed.

  Lemma arg_ptr0 : rdn ASEGS VM (Z_to_bv 64 (sp0z + 8)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) 0)).
  Proof.
    pose proof lay as (_ & HT & LA & LE & VS & _). pose proof arg_facts as (F1 & _ & _ & _ & US0 & _).
    apply (slot_main 8 e_str0 _ F1); [lia | lia |].
    apply bv_eq. change (bv_unsigned (edenot E e_str0)) with (uE E e_str0). rewrite US0, (u_ptr 0 ltac:(lia)).
    replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity. lia.
  Qed.

  Lemma arg_ptr1 : (2 <= length argv)%nat -> rdn ASEGS VM (Z_to_bv 64 (sp0z + 16)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) 1)).
  Proof.
    intros H2. pose proof lay as (_ & HT & LA & LE & VS & ST). pose proof arg_facts as (_ & F2 & _ & _ & _ & US1 & _).
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V1 & _).
    pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp (in_execfn inp))).
    unfold kw_argv1 in F2. apply (slot_main 16 e_argv1w _ F2); [lia | lia |].
    apply bv_eq. rewrite (u_ptr 1 ltac:(lia)).
    unfold e_argv1w. cbn [edenot]. rewrite u_mul64, u_sltu64, u_lit64a.
    change (bv_unsigned (ev E V_ARGC)) with (vE E 1). rewrite V1. change (1 mod 2 ^ 64) with 1.
    replace (1 <? argc) with true by (symmetry; apply Z.ltb_lt; lia).
    change (bv_unsigned (edenot E e_str1)) with (uE E e_str1). rewrite US1, Z.mul_1_l.
    assert (T1 : forall l : list (list byte), (2 <= length l)%nat -> total_arg_bytes_nat (firstn 1 l) = (length (nth 0 l []) + 1)%nat).
    { intros [|x0 l0] Hl; cbn [length] in Hl; [lia|]. cbv [firstn fold_right total_arg_bytes_nat nth]. lia. }
    rewrite (T1 _ H2).
    pose proof Vav as (_ & _ & Hs & _ & _). pose proof (proj1 (Forall_forall _ _) Hs _ (@nth_In _ 0 argv [] ltac:(cbn [length]; lia))) as L0. cbv beta in L0.
    rewrite Z.mod_small; lia.
  Qed.

  Lemma wa_word0 : forall x : word, Z_to_bv 64 (bv_unsigned x) = x.
  Proof. intros x. exact (wa_word x). Qed.

  Theorem pre_args : forall (i : nat) (s : list byte), (i < 2)%nat -> nth_error argv i = Some s -> exists p : Z,
    rdn AsanUbsan.M.loaded_segments VM (Z_to_bv 64 (bv_unsigned sp0 + 8 + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 p))
    /\ astr_at VM sp0 p s.
  Proof using sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh mbase HC Vlau.
    intros i s Hi Hs. change AsanUbsan.M.loaded_segments with ASEGS.
    assert (Hk : (i < length argv)%nat) by exact (nth_error_lt _ _ _ Hs).
    assert (Hn : nth i argv [] = s) by exact (nth_error_nth _ _ [] Hs).
    exists (bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) i)). split; [| rewrite <- Hn; apply arg_string; exact Hk].
    rewrite wa_word0.
    destruct i as [|[|i]]; [ | | lia].
    - replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (sp0z + 8) by lia. apply arg_ptr0.
    - replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 1) with (sp0z + 16) by lia. apply arg_ptr1. lia.
  Qed.
End AT_MAIN.
