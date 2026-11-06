(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsPrintfFirst AF_atexit AXFuzz_stmt AsDrvDefs AsMainPre.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan
  AsImages AsPlanImages AsHSTab AsStartupHSF AsMainVM AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface AsMainIfacePre LazyRestrict LazySR.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsMainSyms.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

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
  (* [comment removed for export] *)
  #[local] Notation VM := (pm_vmem (bv_unsigned sp0) (bv_unsigned brk0) (Xof g E) FULL).
  (* [comment removed for export] *)
  Let MC : PMC sp0 rdraw inp brk0z X FULL := PMC_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC.
  Let SOK : pm_syms_ok sp0z brk0z 0 X := pm_syms_ok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
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


  (* [comment removed for export] *)
  #[local] Notation img_none_main := (AsMainIfacePre.img_none_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation rom_cell_main := (AsMainIfacePre.rom_cell_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation cells_main := (AsMainIfacePre.cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation pre_tid_rdn := (AsMainIfacePre.pre_tid_rdn sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pre_can_rdn := (AsMainIfacePre.pre_can_rdn sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation stack_shadow_zero := (AsMainIfacePre.stack_shadow_zero sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pre_relro : arelro_none VM.
  Proof. exact (img_none_main 0x115000 0x11d000 ltac:(vm_cast_no_check (@eq_refl bool true))). Qed.
  Lemma pre_ro : aro_none VM.
  Proof. exact (img_none_main 0x10000 0x4d000 ltac:(vm_cast_no_check (@eq_refl bool true))). Qed.
  Lemma pre_glb : aglb_none VM.
  Proof.
    split; [exact (img_none_main 0x11fd18 0x11fd20 ltac:(vm_cast_no_check (@eq_refl bool true)))
           | exact (img_none_main 0x11fe08 0x125dc0 ltac:(vm_cast_no_check (@eq_refl bool true)))].
  Qed.
  (* [comment removed for export] *)
  Lemma pre_prist : aprist_none VM.
  Proof.
    intros i [Hi|Hi].
    - exact (img_none_main 0x11fa70 0x11fc20 ltac:(vm_cast_no_check (@eq_refl bool true)) i Hi).
    - exact (img_none_main 0x65bb90 0x65c950 ltac:(vm_cast_no_check (@eq_refl bool true)) i Hi).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pre_cells : cells_ok VM (adrv_cells false).
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma pre_out : cells_ok VM astdout0.
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  (* [comment removed for export] *)
  Lemma pre_axtab : rw_cells asegs VM A_ATEXIT (aatexit_tab false).
  Proof. apply img_cells_main. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma pre_tid : atid_cell VM (ps_tid X).
  Proof. destruct pre_tid_rdn as [RD RG]. split; [exact RD | lia]. Qed.
  Lemma pre_can : exists can, acanary VM can.
  Proof. destruct pre_can_rdn as [can [RD RG]]. exists can. split; [exact RD | exact RG]. Qed.

  (* [comment removed for export] *)
  Lemma pre_latch0 : rdn RSEGS VM (Z_to_bv 64 0x65bad0) 1 = Some [Z_to_bv 8 0].
  Proof.
    pose proof (rom_cell_main (0x65bad0, 1%nat, 0) ltac:(vm_cast_no_check (@eq_refl bool true))) as RD. unfold cell_ok in RD.
    exact RD.
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pre_sh0 : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    forall lo, page_down sp0z - 8388608 <= lo <= 2 ^ 47 -> exists shi, stack0 VM lo shi /\ 0x800000000000 <= shi.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.HeapCeil); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(sp0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainSyms.page_down); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainIface.pd_facts); constr:(brk0); constr:(rdraw); constr:(inp); constr:(h); constr:(ch); constr:(E); constr:(R); constr:(FULL); constr:(model); constr:(Vsp); constr:(Vbrk); constr:(Vav); constr:(Vev); constr:(Hh); constr:(HC); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@kc__1); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsStack0.stack0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainIface.pm_vmem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainFacts.Xof); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainFacts.hole_granted); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.addressable); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.SHAD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.shadow_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u8arr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.asegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.sh); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Lists.ListDef.repeat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainLazy.SHOFF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainIface.u8arr_constZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsMainIfacePre.stack_shadow_zero); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.shadow_of_mult8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.ASegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.As.AsShadow.ASHADOW_BASE_val)|] [|@shi; @z; @Ha; @a; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__p1; @__arith; @__sat8; @__sat7; @zh; @H0; @H6; @H12; @H16; @H15; @H14; @H13; @H11; @H10; @H9; @H8; @H7; @H5; @H4; @H3; @H2; @H1; @H; @__sat4; @__sat5; @__sat6; @g; @__p2; @l; @__sat10; @__sat9; @__x6; @Hz; @AC; @__sat1; @__sat0; @PD3; @PD2; @PD1; @Hlo; @lo; @Hh'; @HCEIL|] "#3B#K$i#P$H$I$G#q##$P#$#K$N#%#)#|#($T#'#&#*$,#.$2#;#+#6#/$>$Q#V#W#_#5#<$g#a#b#d#f#-$0$/#=#>$:#,$`$c#Q#S#`#c#e#g#h#i#j#k#l#m#s#0$'$7$=$<$@$S$[$\$Z$_#B$b#7#4#:#3$m#8#x#r#[#^#w#v#u$?$C$D$F$R$Y$]$^#1$a$e$d$h$i$k$l$j#C#H#G#F#J$o$n$p$q$r#N#Z#U#Y$E$L$K#O$4#n#o$J#]$A#R$%$V#X$O$5#p$6$9$M$U$W$3#y$$$&$($)$*$+$-$;$1$B#~$8$X#T#t$.#z$f#\#{#}$#U$8%$9$$:%$;+$<'$=*$>&$?&$@%$A%$B*$C$$D'$E%$F%$G&$H$$I%$J%$K%$L$$M&$N%$O&$P&$Q%$R'$S%$T%$U%$V%$W%$X%$Y%$Z&$[&$\%$]%#6$$^%$_)$`$$a'$b%$c)$d'$e%$f%$g&$h%USAH$S.$#$#$#$#$#L#VSB#S/$%$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3#05#)C>#USc70#&##H3A.B.#.#.#3#Q(##H#%+#dSdS/S0SCS4S5SDS6SES7SFSGSHSISJSKSL#/s#$3?,1#+s#'#%&#.S..#.#.#.#.#.#.#.#.#.#.#.#.#.#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3###s#C$s#H$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3##s#]#%=#6s#_s#Q)C#G%%#%s#Q#VSBs#yS0USeS5VSf#S6XSgs#{%#S7MN#RH#.H%$#j#$C#VSMC#j##,#MS8)S)H%#(j#$C#VSMC#j##2#MSN.S&H%#-j#$C#MS+1S8s#l#<s#m6Hs#i0H#)C#s#xj#%C#Rs#xs#s+Gs#y#Gs#u+Gs#uk##$#k##&##Gs#~Ss$#s#zJj##O#j#&%##Gs#|k##O#k#&(#Hs$.s#z#Gs$/#Gs#|6s$1s#}#G#k##%#k##'#Ts$Hs$%#Gs$I>s$Js$'#G#k##+#k##&#1&s$+H#s$,#G$6%s$.#G#k##2#k##&#?s$Us$2)Cs$3GUSO#1s$506s$Ys$6,$#)Cs$[#k##'#@s$]s$:+Gs$;#G(+)s$=%$#k##&#As$cs$@+s$AG+s$B.#/G%$#k##&#Bs$is$F)CBGk##7#Cs$ls$I)C6s$mk##:#Ds$os$Lm#S%#?s$^s$N>s$_s$O1s$P#,#s#2)Cs$b#k##A#@s$ds$T+s#6s$U%s#6#k##>#As$hs$X+s$Ys#:#s#;G%$#k##=#Bs$ms$])C1Gk##s#.#Cs$ps$`)Cs#Bs$qk##s#1#Ds$ss$cm#S%#?s#<s$e>s#=s$f1s$g#,#s#<)Cs#@#k##s#8#@s#Bs$k+s#@s$l%s#@#k##s#5#As#Fs$o+s$ps#D#s#EG%$#k##s#4#Bs#Ks$t)C1Gk##s#E#Cs#Ns$w)Cs#Ls#Ok##s#H#Ds#Qs$zm#S%#VS9Gs$|NS:#m##s#EUR#I$US1%VS;HJj#'s#n#k#'s#os#kVS9Gs%4NS:#m##s#wUS<#7SP7#7#7#7#5C#5CSP*C$#3s$]VS=C#8C#&VS=Cs%87*7#7#5C#8C'#USQs%[VSRC#5C)EC$#5C48C-#5C78C/#*C%#*C(#*C-#*C4#J#S,<9#USQS.VSRC#EC#>*C#>5C8EC&/*CB#*C5#*C&#5Cs#*8C@#8CAs#&*C$#J#S,<(#<.#UShS'FS'$#FS'5#USSS'GCPUSiC/C$P#/C#M$GCR/C&S##/C%J#USjCUSkC9CG4Cs&8'C$L#(&FDDE#I9Cs%m'C&S-#()FDDE#I-*FDDE&#USlD'C'Q+(-FDDE#IZST.FDDE#4CS.9Cs&+:C$#4Cs&D;C.#2C#2'C&Q#(6FDDE#I&7FDDE+.#4Cs%y'C8L#(:FDDE#I'C%S-6(<FDDE#I-=FDDE%#4Cs&$;C:#2C#*'C4Q#(BFDDE#I&s##FDDE7:#9Cs%X;C)@'C$L#(s#'FDDE#IKs#(FDDES$-s#)FDDE$#:C;s#(:C(='C$Q#(s#-FDDE#I&s#.FDDE's#%#&s#/FDDE.s#&#&s#0FDDE5s#'#&s#1FDDE<s#(#&s#2FDDEs#*s#)#VSms#3ENSUSVVSnHM)SU#SVm$%#WSoCGJXSWHM$#l#(*)#l#)s#=s#<#l#*s#Fs#E#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K##GJ+Js&N%$#k##s${SX0Ms&b1s&RN,#S#)C%#k##'##GP+Ps&W%$#,)S$)CR#k##-#1Ns&\#s&+#%#S>0Ps&p0#N1S$s&a0#s&s)C%#k##(#k##,#k##0#k##4#k##;#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K##s%Fs&#_H#s%#s%<s%Ks%Qs'7PS1RS(SYl#1s#'%#l#2s$Hs%_#l#3s$Ns$M#l#4S#O#l#5s$Rs%9#l#6s$Ts$~#l#7s$Vs$h#0s',s%Y0s%Ps'.)C$#m#&#l#8s$_s$`#l#9s$ds$b#l#:s$hs$f#l#;s$ns$j#l#7s$ss$p#l#<s$zs$u#l#=s$|s$}#l#>s%%s%##l#?s%)s%'#l#@s%/s%+#l#6s%4s%1#l#As%;s%6#l#Bs%=s%>#l#Cs%Bs%@#l#Ds%Fs%D#l#Es%Ms%H#l#5s%Ts%O#l#Fs%]s%V#l#Gs%ds%_#l#Hs%ls%g#l#Is%ts%n#l#3s%ys%v#l#2s&'s%~#)C=s'Dm#$#USAS+OCs'Js&,$#S&US?S+)C#s'Im#%#US?Sp##H#HS+%$##S+s'G#s'HSq%$#0s'JH3s'n6$#)C#GWSZs&OH&%$#%)#%-#j#JC#US?SN#HH%#2%#(j#%C##s'`s'`#s'aS&%$##S&s'[#s'\s'\%$#0s'^s'f6#6)C#GWSZs&bs'i%%$#%(#Hs'ms'_#Gs'n#Gs&nk##s&D#k##%#?s'rs'd>s'ss'e1s'f#,#s&t)Cs'v#k##s&7#@s'xs'j+s&xs'k%-#k##s&4#As'|s'n+s'os&|#s&}G%$#k##s&3#Bs(%s's)C1Gk##s&D#Cs((s'v)Cs'(s()k##s&G#Ds(+s'ym#S%#VS8HJj#'s&g#Is%TGCM/C#Js$|'Cs$gLs$t(s$wFDDE#IKs$xFDDER-s$yFDDE$#'Cs$kLs$k(s${FDDE#I-s$|FDDE#'&s$}FDDE&s$t#l#(#s$Ms$Gl#),s%$#l#*s%0s%-#j#+C#j#,C#j#0K#0Hs(C##J%#M0Js(F####$M%$#k##'#k#+C#k#,C#k#0K##S2s(BXH#S2s(LS(l#10%#l#IAs'-#l#Hs##s%w#l#4JO#l#5s%~s#5##s(QS[%s#P#m#%#l#Bs#+s#,#l#Cs#0s#.#l#Ds#4s#2#l#Es#:s#6#l#5s#?s#<#l#Fs#Fs#A#l#Gs#Ls#H#l#Hs'6s'3#l#Is'@s';#GCJKs%GFDDES#9Cs(]Ls(ZWS@C$#'Cs%>L#(s%LFDDE#I-s%MFDDE(#'C&L&(s%OFDDE#I-s%PFDDE&#&s%QFDDE&s%H#l#(#s$}s$wl#)/s%T#l#*s%`s%]#j#+C#j#0K#%Js(e#Js(g%#s#jk##%#k#+C#k#0K##s(tS2WH#S2S(l#1+%#l#Is#Ks'W#l#Hs#Ms&E#l#4JO#l#5s&Ls#_##S[s(s%#s#vm#%#l#Bs#Us#V#l#Cs#Zs#X#l#Ds#^s#\#l#Es#ds#`#l#5s#is#f#l#Fs#ps#k#l#Gs#vs#r#l#Hs'`s']#l#Is'js'e#Hs$#s$6#Gs$$#Gs$8#Gs$%k##$#k##&#?s$)s$<)Cs$=GUSO#>s$,s$?1s$@#,#s$-)Cs$/#k##'#@s$1s$D+Gs$E+s$2s$F%0#k##%#As$6s$I+s$JG+s$Ks$7#s$8G%$#k##&#Bs$<s$O)C3Gk##6#Cs$?s$R)Cs$?s$@k##9#Ds$Bs$Um#S%#VS9Gs$WNS:#m##6I#VS1HJj#'s(/#US*s&xECs&Ws&T*Cs&Ts&r*Cs&X#*C%#*Cs&hs&f*Cs&Y#*Cs&n#*Cs&Vs&xJ#S,<%#<)#FS'#s&S/Cs&LMs&OGCS#/C$P#/Cs&QPs&R/C$J#4Cs*$.s*%4C#;Cs&K#$s)W4C#2C%#'C)Q#(s&UFDDE#I&s&VFDDEs&Js&M#9Cs$y'Cs&KS-#(s&YFDDE#I-s&ZFDDEs&4#'C&Qs&Z(s&\FDDE#IZSTs&]FDDE#:C3s&P:Cs#s#;C+s&P2C#s&T'C%Q#(s&cFDDE#I&s&dFDDE)s&[#'Cs&dL((s&fFDDE#I'Cs&fL2(s&hFDDE#I'Cs&hLs&\(s&jFDDE#I&s&kFDDE%s&b#&s&lFDDE(s&c#'C=Qs&l(s&nFDDE#I'Cs&MLs#$(s&pFDDE#I9Cs)/'Cs#'L#(s&sFDDE#I-s&tFDDE&#'Cs&hQs&t(s&vFDDE#I&s&wFDDE%s&n#&s&xFDDE,s&o#&s&yFDDE/s&p#&s&zFDDE8s&q#&s&{FDDEs##s&r#&s&|FDDEs#(s&s#l#(#s&Ls&Fl#)s#4s'##l#*s#:s',#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#1s*4P,#S#)CM#k##s&E#+Js%P%N#k##s#sSX0Rs*L0s*A#1s%UN,#S#)C%#k##(##G'k##s$$s&Jk##$#)CNG#s)oN#Ns)V%$#k###&k##'#k##)#k##-#k##5#k##8#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K#`Hs$5s%Ms$/s)as*bs%XS&RS\S*S]S(l#1s#$$#l#3s#os)C#l#Is#qs(1#l#4MO#l#5s#us$,#l#6s(9s%L#m##s%^l#=s%@s%A#l#>s%Es%C#l#?s%Is%G#l#@s%Os%K#l#6s%Ts%Q#l#As%[s%V#l#Bs$&s$'#l#Cs$+s$)#l#Ds$/s$-#l#Es$6s$1#l#5s$<s$8#l#Fs$Es$>#l#Gs%gs%c#l#Hs$Ms$H#l#Is)Rs)O#l#3s)\s)W#USrs%qWSss)ss*z#'Cs'WLs#Q(s'eFDDE#I-s'fFDDEs$}#:Cs${s'X'Cs'gL#(s'iFDDE#I&s'jFDDE&s'a#l#(#s':s'4l#)s%(s'm#l#*s'ys'v#j#+C#j#0K##Hs*.%J#0s+%s%I#G#k##%#k#+C#k#0K#WHs*Ns+3S^l#1+$#l#Is%ds)p#l#Hs%fs(^#l#4JO#l#5s(es%x#m##s$jl#Bs%ls%m#l#Cs%qs%o#l#Ds%us%s#l#Es%{s%w#l#5s&$s%}#l#Fs&+s&&#l#Gs&1s&-#l#Hs)ws)t#l#Is*%s)|##Gs+B6s+Cs&N)C#GUSts+EPS3s*?#s#+%%#'Cs'kLs($(s(2FDDE#I-s(3FDDE#s%J'Cs(3Ls(%(s(5FDDE#I&s(6FDDE%s(-#l#(#s'bs'\l#)s%Ps(9#l#*s(Es(B#j#+C#j#0K##s*pH%#J#Gs%qk##$#k#+C#k#0K#WHs*[s+ZS^l#1*$#l#Is&/s*;#l#Hs&1s))#l#4JO#l#5s)0s&C#m##?l#Bs&7s&8#l#Cs&<s&:#l#Ds&@s&>#l#Es&Fs&B#l#5s&Ks&H#l#Fs&Rs&M#l#Gs&Xs&T#l#Hs*Bs*?#l#Is*Ls*G#Hs+is&t#Gs#)k##s%@#k##s#,#?s+ms&x>s+ns&y1s&z#,#s#/)Cs+q#k##s%A#@s+ss&~+s#3s'#%-#k##s%>#As+ws'&+s''s#7#s#8G%$#k##s%>#Bs+|s'+)C1Gk##s%N#Cs,#s'.)Cs#?s,$k##s%Q#Ds,&s'1m#S%#ECs),s)95Cs)LECs).#*Cs):#*Cs)K#*C'#*Cs);s)**Cs)2#*Cs)1#<#s%4<'#FS'#s)('Cs$yQs$v(s(zFDDE#I&s({FDDEs$|s(r#'Cs({Ls$|(s(}FDDE#I&s(~FDDE#s(us$qKs)#FDDES)-s)$FDDEs$n#&s)%FDDE#s(xs$i&s)&FDDEs$rs(y#&s)'FDDE's(z#&s)(FDDE+s({#&s))FDDEs%-s(|#&s)*FDDEs%2s(}#l#(#s(Vs(Pl#)s%>s)-#l#*3s)6#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#j#KK#)Cs$bs$_k##s$d##Gs$dk###s$^%s$\S&k###s$^k##s$_#k##&#k##)#k##s$m#k##s$p#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K#k#KK#aHs+`s#Rs'Js#Ns+^s,_s#yS&RS\S*S]S(l#16$#l#3s%ls+@#l#Is%ns*.#l#4MO#l#5s%rs#L#l#6s*6s'I#m##s$#l#=s'=s'>#l#>s'Bs'@#l#?s'Fs'D#l#@s'Ls'H#l#6s'Qs'N#l#As'Xs'S#l#Bs#Gs#H#l#Cs#Ls#J#l#Ds#Ps#N#l#Es#Vs#R#l#5s#[s#X#l#Fs#bs#]#l#Gs'ds'`#l#Hs#hs#e#l#Is+Os+L#l#3s+Ys+T#3s,H,Hs#gPS3s+q#s$]j#%C#Ls-9USu#USS#USvGUSws&LWSx&$#,S_s#pPS3s+z#Hj#L(#Ts-'s(2#Gs#tk##s&Z#k##s$F#/Cs'ZMs)w/C#Js)x-s)rFDDEs%`s'X9C62C#s)g'Cs)tL#(s)vFDDE#I&s)wFDDE's)n#&s)xFDDEs#Xs)o#l#(#s)Hs)Bl#)+s){#l#*s*+s*(#j#+C#j#,C#j#0K##GMk##s&l#k##s$E##s,ZM%#S#,s#'M#G#k##%#k##(#k#+C#k#,C#k#0K#YHs,Hs-Gs$6S*S(l#10$#l#3s&Ts,(#l#Is&Vs*r#l#4MO#l#5s&Zs$4#l#6s*zs(1#,s#5s$=#G#m#%#l#=s('s((#l#>s(,s(*#l#?s(0s(.#l#@s(6s(2#l#6s(;s(8#l#As(Bs(=#l#Bs$1s$2#l#Cs$6s$4#l#Ds$:s$8#l#Es$@s$<#l#5s$Es$B#l#Fs$Ls$G#l#Gs(Ns(J#l#Hs#8s#5#l#Is,9s,6#l#3s,Cs,>##Gs#>m#$#Ts(Zs(m#Gs'1k##s'9#k##s';#-s*OFDDEs(5s&:&s*PFDDE#s*Gs&D&s*QFDDEs&Cs*H#l#(#s)}s)wl#)s#@s*T#l#*s*`s*]#j#+C#j#,C#j#0K#k##s%Cs#6#Ms,s%S##k###s#:k##&#k#+C#k#,C#k#0K#YHs-7s-xs'ES*S(l#1,$#l#3s')s,Y#l#Is'+s+G#l#4MO#l#5s'/s'B#l#6s+Os(b#m##=l#=s(Vs(W#l#>s([s(Y#l#?s(_s(]#l#@s(es(a#l#6s(js(g#l#As(qs(l#l#Bs'<s'=#l#Cs'As'?#l#Ds'Es'C#l#Es'Ls'G#l#5s'Rs'N#l#Fs'[s'T#l#Gs(}s(y#l#Hs#,s#)#l#Is,hs,e#l#3s,rs,m#3s.KRs.2##G$Qs.4%+G#k##%#k##s,x#Ss.8)Jj##O#j#&s,v##G)k##O#k#&s,y#US1s'Pk#'s,{&VSYHJj#'s,}#USys+jVS=Cs)P8C#s+d*Cs+G#*Cs+W#*Cs+L#*Cs+[#J#S,FS'#s+A/Cs+=Ms+</Cs+;S#s+>/C#Ps+?/C%J#$s.N4C#'Cs+;L#(s+=FDDE#I-s+>FDDE#s*t4Cs.S:C#s+2:Cs(U#;Cs'Is+@2C#*'C%Q#(s+EFDDE#I&s+FFDDEs'Gs+=#'Cs+FLs'V(s+HFDDE#I-s+IFDDE#s%(;Cs'Qs+=2C#s'Z'C.Q#(s+MFDDE#I&s+NFDDEs'Os+E#'Cs+-L2(s+PFDDE#I'C4Ls'>(s+RFDDE#I-s+SFDDE%#2Cs$>s+RWS@Cs(ks/''C$L#(s+WFDDE#I&s+XFDDE's+O#&s+YFDDE-s+P#&s+ZFDDE3s+Q#&s+[FDDE7s+R#&s+\FDDE@s+S#l#(#s+,s+&l#)s#'s+_#l#*s#,s+h#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#j#KK##GR%#P1s*/S#,#N)Cs';#k##s'>#%s+#S)0Ns/-1s*5R,#S$)C%#k##s'D#,s$rP,#N##s#Xk##s';#k##'#k##-#k##/#k##4#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K#k#KK#`Hs&'s(`s*4s&Xs/>s(gs&-S)S`S$S<Szl#1?$#l#Ms#Ys-{#l#Ns#[s,i#l#4NO#l#2s,gs#h#l#3s,ms#`#l#4S#O#l#5s#cs&.#l#6s(Us(h#l#7s,us*,#,s$Ys(r##s#qm#%#l#8s)~s*##l#9s*'s*%#l#:s*+s*)#l#;s*1s*-#l#7s*6s*3#l#<s*=s*8#l#=s(ds(e#l#>s(is(g#l#?s(ms(k#l#@s(ts(o#l#6s(zs(v#l#As)'s(|#l#Bs&2s&3#l#Cs&7s&5#l#Ds&;s&9#l#Es&As&=#l#5s&Fs&C#l#Fs&Ms&H#l#Gs*Os*K#l#Hs$Zs$W#l#Is%:s%7#l#3s$&s$##l#2s$/s$*#l#Ns.=s.:#l#Ms.Gs.B#,s%Bs)2##s$1m#%##s%EH+H&%$#$s/f$#3#Rs/k##G$Qs/m%+G#k##%#k##s.U#Ss/q)Jj##O#j#&s.S##G)k##O#k#&s.V#k#'s.W%8Cs$7s-+*C#s$7*Cs-##*Cs-2#*Cs)-#*Cs-8#J#S,FS'#s,v/Cs,sNs,r/Cs,sM#GCN/C#Ns,u/Cs$:N#/C&J#4Cs0('Cs,qL#(s,sFDDE#I-s,tFDDE#s&S;Cs(|s)(2C#''Cs$8Q#(s,xFDDE#I&s,yFDDEs(zs,p#Ks,zFDDES>-s,{FDDEs$@#2Cs$4s$C'Cs$?Q#(s,~FDDE#I&s-#FDDEs)$s,v#'Cs%jLs,~(s-%FDDE#I2Cs%ls)5'Cs-%S-#(s-(FDDE#I-s-)FDDE&#Ls#4WS@Cs*A#2Cs%s#'Cs-+S-#(s-.FDDE#I-s-/FDDE,#&s-0FDDEs$;s-'#&s-1FDDE*s-(#&s-2FDDE1s-)#&s-3FDDE6s-*#&s-4FDDE9s-+#&s-5FDDE?s-,#l#(#s,as,[l#)s#%s-8#l#*s#,s-A#j#+C#j#,C#j#-C#j#.C#j#/C#j#OC#j#0K#j#KK#%s,SN1s+dP,#S$)Cs(p#k##s(s##GN%#S>,s$7S))Cs$9#k##s(x#,s&JR##P,$S$+P#%%##s0(S$#S$s/k%$#,s&RN##S$,s&Ts#[+S$#%%#k##(#k##,#k##2#k##6#k##9#k##>#k#+C#k#,C#k#-C#k#.C#k#/C#k#OC#k#0K#k#KK#bHs'gs*Ds+ts(<s*Ks0~S{s'mS)S`S$S<S|S}l#1s#)$#l#Ms%=s#l#l#Ns%?s#e#l#4NO#l#2s.Ks/b#l#3s.Qs.P#l#4S#O#l#5s%Gs'n#l#6s*9s*L#l#7s.Ys+l##s&=S;+S;?%$#m#&#l#8s+cs+d#l#9s+hs+f#l#:s+ls+j#l#;s+rs+n#l#7s+ws+t#l#<s+~s+y#l#=s*Is*J#l#>s*Ns*L#l#?s*Rs*P#l#@s*Ys*T#l#6s*_s*[#l#As*hs*a#l#Bs'ss't#l#Cs'xs'v#l#Ds'|s'z#l#Es(&s'~#l#5s(+s((#l#Fs(2s(-#l#Gs,4s,0#l#Hs&?s&<#l#Is&{s&x#l#3s/|s/y#l#2s0*s0%#l#Ns$0s$-#l#Ms$9s$4##s''J,S_s$9+J#%%#m#'#fS~S/S0SCS4S5SDS6SES7SFSGSHSISJSKSLJ#j#Ps$D#j#%C#_T#S/S0S4s0Js'/s*{Gs&Ns%}s$I#URs/&Is.zXSWHMs-gs-cl#(s)2s-i#l#)s+Ws.@#l#*s.Ls.I#j#+C#j#0K#l#1#s)+s)*l#I*s0;#l#Hs,1s/)#l#4JO#l#5.s,C#l#BS%s,7#l#Cs,;s,9#l#Ds,?s,=#l#Es,Es,A#l#5s,Js,G#l#Fs,Qs,L#l#Gs,Ws,S#l#Hs0As0>#l#Is0Ks0F#Is*yUS*s/4l#(s*5s-~8l#)s*fs.U#l#*s*ls.^#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#l#1#s)qs)pl#3-s0T#l#Is+&s/B#l#4MO#l#51s+=#l#6s#(s,]#l#=S%s,Q#l#>s,Us,S#l#?s,Ys,W#l#@s,_s,[#l#6s,ds,a#l#As,ks,f#l#BS%s+7#l#Cs+;s+9#l#Ds+?s+=#l#Es+Fs+A#l#5s+Ls+H#l#Fs+Us+N#l#Gs,ws,s#l#Hs+]s+X#l#Is0bs0_#l#3s0ls0g#WT$s-%s#$#Os'ls'is'fs#;s)o#PS3s1(s'@s)pm#$#OCs'us'r#T%T&m##s)J=s)Ms)Ks'x#=s)Ps)Ks)*#m##s)u=s+hs)vs)S#m##s-,=s-.s--s)z#=s-2s--s+m#=s-6s--s,<#%s-6s-I%#s-0%s-9#m#&#OCs2?s->#s-BHXSaCs-Ds-C#l#Qs-Us-V#UJs/h'Cs*uLs,@(s/-FDDE#Il#(#s.Ys.Sl#)s/6s/0#l#*s/<s/9#l#1#s11Hl#R)s1)#l#Ss1%s0~#l#Rs1/s1*#=s16s15-#XSaCs18s2E#j#Ts1M#j#Us1P#V#JHj##s1P#j##s1S#YSbs1Ts1Rs1A#Hj#Fs1R#j#Vs2E#V#JHj##s1U#j##s2H#YSbs2Is1Ws1L#Hl#Fs2Os1W#j#Ws2Q#j#XC#j#Ys2_#j#ZT'##"). Qed.
End AT_MAIN.
