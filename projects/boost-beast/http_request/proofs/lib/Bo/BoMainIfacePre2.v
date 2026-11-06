(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsStack0 AsPrintfFirst AF_atexit AXFuzz_stmt AsDrvDefs AsMainPre.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan BothImages BothPlanImages AsHSTab BoStartupHSF AsMainVM BoMainState BoMainFacts BoMainLazyChk BoMainLazy BoMainCells BoMainIface BoMainIfacePre LazyRestrict LazySR.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AsMainSyms.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk BSEGS2 brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Vfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Hh : HSF_both h = Some ch.
  Hypothesis HC : cs_ok BSEGS2 BOTH_H AsanInit.LIMIT (SINV0 BPH2 sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                        (argH0 BPH2 sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.
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
  #[local] Notation kp_apart := (BoMainIface.kp_apart sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_apart_ne := (BoMainIface.kp_apart_ne sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_facts := (BoMainIface.kp_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_align := (BoMainIface.kp_align sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pd_facts := (BoMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b06 := (BoMainIface.kp_b06 h E) (only parsing).
  #[local] Notation kp_b08 := (BoMainIface.kp_b08 h E) (only parsing).
  #[local] Notation kp_b22 := (BoMainIface.kp_b22 h E) (only parsing).
  #[local] Notation vm_full := (BoMainIface.vm_full sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_img := (BoMainIface.vm_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_S := (BoMainIface.vm_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_obj := (BoMainIface.vm_obj sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_ri := (BoMainIface.vm_ri sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_stack := (BoMainIface.vm_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_brk := (BoMainIface.vm_brk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation seg_rom_above := (BoMainIface.seg_rom_above sp0 brk0 inp) (only parsing).
  #[local] Notation seg_rom_below := (BoMainIface.seg_rom_below sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_above := (BoMainIface.mrd_above sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_outside := (BoMainIface.mrd_outside sp0 brk0 inp) (only parsing).
  #[local] Notation vrange := (BoMainIface.vrange sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_sub := (BoMainIface.vr_sub sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_img := (BoMainIface.vr_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_stack := (BoMainIface.vr_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation G_cases := (BoMainIface.G_cases sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zinP_of_In := BoMainIface.zinP_of_In (only parsing).
  #[local] Notation vr_kobj_gen := (BoMainIface.vr_kobj_gen sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b04 := (BoMainIface.kp_b04 h E) (only parsing).
  #[local] Notation kp_b05 := (BoMainIface.kp_b05 h E) (only parsing).
  #[local] Notation kp_b09 := (BoMainIface.kp_b09 h E) (only parsing).
  #[local] Notation kp_b10 := (BoMainIface.kp_b10 h E) (only parsing).
  #[local] Notation kp_b11 := (BoMainIface.kp_b11 h E) (only parsing).
  #[local] Notation kp_b12 := (BoMainIface.kp_b12 h E) (only parsing).
  #[local] Notation kp_b16 := (BoMainIface.kp_b16 h E) (only parsing).
  #[local] Notation kp_b20 := (BoMainIface.kp_b20 h E) (only parsing).
  #[local] Notation kp_b21 := (BoMainIface.kp_b21 h E) (only parsing).
  #[local] Notation kp_b23 := (BoMainIface.kp_b23 h E) (only parsing).
  #[local] Notation vr_b04 := (BoMainIface.vr_b04 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b05 := (BoMainIface.vr_b05 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b09 := (BoMainIface.vr_b09 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b10 := (BoMainIface.vr_b10 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b11 := (BoMainIface.vr_b11 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b12 := (BoMainIface.vr_b12 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b16 := (BoMainIface.vr_b16 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b20 := (BoMainIface.vr_b20 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b21 := (BoMainIface.vr_b21 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b23 := (BoMainIface.vr_b23 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_sw := (BoMainIface.vm_sw sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_b22 := (BoMainIface.vm_b22 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation world_ok_X := (BoMainIface.world_ok_X sp0 h E) (only parsing).
  #[local] Notation bytes_main := (BoMainIface.bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation word_main := (BoMainIface.word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zero_main := (BoMainIface.zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fill_main := (BoMainIface.fill_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation bytes_at_const := (BoMainIface.bytes_at_const sp0 brk0 inp) (only parsing).
  #[local] Notation u8arr_const := (BoMainIface.u8arr_const sp0 brk0 inp) (only parsing).
  #[local] Notation bytes_at_constZ := (BoMainIface.bytes_at_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_img := (BoMainIface.rw_cells_img sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_above := (BoMainIface.rw_cells_above sp0 brk0 inp) (only parsing).
  #[local] Notation cellsZ := BoMainIface.cellsZ (only parsing).
  #[local] Notation cells_wfb := BoMainIface.cells_wfb (only parsing).
  #[local] Notation cells_wfb_sound := BoMainIface.cells_wfb_sound (only parsing).
  #[local] Notation map_b8_unsigned := BoMainIface.map_b8_unsigned (only parsing).
  #[local] Notation map_b8_cellsZ := BoMainIface.map_b8_cellsZ (only parsing).
  #[local] Notation length_cellsZ := BoMainIface.length_cellsZ (only parsing).
  #[local] Notation img_cells_check := BoMainIface.img_cells_check (only parsing).
  #[local] Notation img_cells_main := (BoMainIface.img_cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation lowsh_vm := (BoMainIface.lowsh_vm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation lowsh_vis := (BoMainIface.lowsh_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation u8arr_constZ := (BoMainIface.u8arr_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation fact_ivl := BoMainIface.fact_ivl (only parsing).
  #[local] Notation ivls_of := BoMainIface.ivls_of (only parsing).
  #[local] Notation cover_sweep := BoMainIface.cover_sweep (only parsing).
  #[local] Notation cover_check := BoMainIface.cover_check (only parsing).
  #[local] Notation cover_sweep_sound := (BoMainIface.cover_sweep_sound sp0 brk0 inp) (only parsing).
  #[local] Notation ivls_of_In := BoMainIface.ivls_of_In (only parsing).
  #[local] Notation Mr_some' := (BoMainIface.Mr_some' sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_nonnull := (BoMainIface.Mr_nonnull sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation uE_lit' := (BoMainIface.uE_lit' E) (only parsing).
  #[local] Notation estart_lit := (BoMainIface.estart_lit sp0 brk0 inp E) (only parsing).
  #[local] Notation fact_ivl_sound := (BoMainIface.fact_ivl_sound sp0 brk0 rdraw inp ch E R FULL model HC) (only parsing).
  #[local] Notation cover_main := (BoMainIface.cover_main sp0 brk0 rdraw inp h ch E R FULL model Hh HC) (only parsing).
  #[local] Notation lowsh_stk := (BoMainIface.lowsh_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_word_main := (BoMainIface.img_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zscanN := BoMainIface.zscanN (only parsing).
  #[local] Notation zscanN_sound := (BoMainIface.zscanN_sound sp0 brk0 inp) (only parsing).
  #[local] Notation segment_byte_at_zero1 := (BoMainIface.segment_byte_at_zero1 sp0 brk0 inp) (only parsing).
  #[local] Notation obj_word_main := (BoMainIface.obj_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_bytes_main := (BoMainIface.obj_bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_zero_main := (BoMainIface.obj_zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation world_uw := (BoMainIface.world_uw sp0 h) (only parsing).
  #[local] Notation rw_cells_cons1 := BoMainIface.rw_cells_cons1 (only parsing).

  (* [comment removed for export] *)
  #[local] Notation all_holes_w_here := (BoMainCells.all_holes_w_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation all_holes_here := (BoMainCells.all_holes_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation hole_sel_here := (BoMainCells.hole_sel_here sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hole_short_pm := (BoMainCells.hole_short_pm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation csym_den := (BoMainCells.csym_den sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation uE_lit := (BoMainCells.uE_lit E) (only parsing).
  #[local] Notation zero_sound := (BoMainCells.zero_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation fill_sound := (BoMainCells.fill_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation bytes_sound := (BoMainCells.bytes_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation word_sound := (BoMainCells.word_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_sound := (BoMainCells.img_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vav Hh HC) (only parsing).
  #[local] Notation argH0_low := (BoMainCells.argH0_low sp0 brk0 rdraw inp E Vsp Vav) (only parsing).
  #[local] Notation hid_img := (BoMainCells.hid_img sp0 brk0 rdraw inp ch E model Vsp Vav) (only parsing).
  #[local] Notation brk_facts := (BoMainCells.brk_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VISK_bound := (BoMainCells.VISK_bound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VM_Z := (BoMainCells.VM_Z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_vis := (BoMainCells.hid_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_sh := (BoMainCells.hid_sh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_stack := (BoMainCells.hid_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation visibleZ_hid := (BoMainCells.visibleZ_hid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation args_block := (BoMainCells.args_block sp0 brk0 rdraw inp ch E R FULL model Vsp Vav Vev Vfit HC) (only parsing).
  #[local] Notation Mr_some := (BoMainCells.Mr_some sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_vis_none := (BoMainCells.Mr_vis_none sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation rdn_Mr_full := (BoMainCells.rdn_Mr_full sp0 brk0 rdraw inp ch E FULL model) (only parsing).


  (* [comment removed for export] *)
  #[local] Notation img_none_main := (BoMainIfacePre.img_none_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation rom_cell_main := (BoMainIfacePre.rom_cell_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation cells_main := (BoMainIfacePre.cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation pre_tid_rdn := (BoMainIfacePre.pre_tid_rdn sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pre_can_rdn := (BoMainIfacePre.pre_can_rdn sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation stack_shadow_zero := (BoMainIfacePre.stack_shadow_zero sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pre_relro : arelro_none VM.
  Proof. exact (img_none_main 0x119000 0x121000 ltac:(vm_cast_no_check (@eq_refl bool true))). Qed.
  Lemma pre_ro : aro_none VM.
  Proof. exact (img_none_main 0x10000 0x4e000 ltac:(vm_cast_no_check (@eq_refl bool true))). Qed.
  Lemma pre_glb : aglb_none VM.
  Proof.
    split; [exact (img_none_main 0x123fd8 0x123fe0 ltac:(vm_cast_no_check (@eq_refl bool true)))
           | exact (img_none_main 0x1240c8 0x12a100 ltac:(vm_cast_no_check (@eq_refl bool true)))].
  Qed.
  (* [comment removed for export] *)
  Lemma pre_prist : aprist_none VM.
  Proof.
    intros i [Hi|Hi].
    - exact (img_none_main 0x123d30 0x123ee0 ltac:(vm_cast_no_check (@eq_refl bool true)) i Hi).
    - exact (img_none_main 0x65fed0 0x660c90 ltac:(vm_cast_no_check (@eq_refl bool true)) i Hi).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pre_cells : cells_ok VM (adrv_cells false).
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma pre_out : cells_ok VM astdout0.
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  (* [comment removed for export] *)
  Lemma pre_axtab : rw_cells bsegs VM A_ATEXIT (aatexit_tab false).
  Proof. apply img_cells_main. vm_cast_no_check (@eq_refl bool true). Qed.

  Lemma pre_tid : atid_cell VM (ps_tid X).
  Proof. destruct pre_tid_rdn as [RD RG]. split; [exact RD | lia]. Qed.
  Lemma pre_can : exists can, acanary VM can.
  Proof. destruct pre_can_rdn as [can [RD RG]]. exists can. split; [exact RD | exact RG]. Qed.

  (* [comment removed for export] *)
  Lemma pre_latch0 : rdn RSEGS VM (Z_to_bv 64 0x65fe10) 1 = Some [Z_to_bv 8 0].
  Proof.
    pose proof (rom_cell_main (0x65fe10, 1%nat, 0) ltac:(vm_cast_no_check (@eq_refl bool true))) as RD. unfold cell_ok in RD.
    exact RD.
  Qed.
Scheme kc__1 := Elimination for Corelib.Init.Logic.and Sort Prop.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pre_sh0 : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    forall lo, page_down sp0z - 8388608 <= lo <= 2 ^ 47 -> exists shi, stack0 VM lo shi /\ 0x800000000000 <= shi.
  Proof.
    ltac2:(KReplay.run [|constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.HeapCeil); constr:(@Corelib.Init.Logic.eq); constr:(@Corelib.Numbers.BinNums.Z); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.HeapCeil.hceil); constr:(@Stdlib.ZArith.BinInt.Z.sub); constr:(@stdpp.bitvector.definitions.bv_unsigned); constr:(@Corelib.Numbers.BinNums.Npos); constr:(@Corelib.Numbers.BinNums.xO); constr:(@Corelib.Numbers.BinNums.xH); constr:(sp0); constr:(@Corelib.Numbers.BinNums.Zpos); constr:(@Corelib.Init.Logic.and); constr:(@Stdlib.ZArith.BinInt.Z.le); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.page_down); constr:(@Stdlib.ZArith.BinInt.Z.pow); constr:(@Corelib.Numbers.BinNums.xI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainIface.pd_facts); constr:(brk0); constr:(rdraw); constr:(inp); constr:(h); constr:(ch); constr:(E); constr:(R); constr:(FULL); constr:(model); constr:(Vsp); constr:(Vbrk); constr:(Vav); constr:(Vev); constr:(Hh); constr:(HC); constr:(@Stdlib.ZArith.BinInt.Z.lt); constr:(@Stdlib.ZArith.BinInt.Z.add); constr:(@Stdlib.ZArith.BinInt.Z.modulo); constr:(@Corelib.Numbers.BinNums.Z0); constr:(@kc__1); constr:(@Corelib.Init.Logic.ex); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsStack0.stack0); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainIface.pm_vmem); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.Xof); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainFacts.hole_granted); constr:(@Corelib.Init.Logic.ex_intro); constr:(@Corelib.Init.Logic.conj); constr:(@Corelib.Init.Logic.eq_ind_r); constr:(@Stdlib.ZArith.BinInt.Z.pow_pos_nonneg); constr:(@Corelib.Init.Logic.True); constr:(@Stdlib.ZArith.BinInt.Z.pow_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_mod_nonneg_nonneg); constr:(@Stdlib.micromega.SatDivMod.Z_div_nonneg_nonneg); constr:(@Stdlib.ZArith.BinInt.Z.div); constr:(@Stdlib.ZArith.BinInt.Z.mul); constr:(@Stdlib.ZArith.BinInt.Z.div_mod); constr:(@Corelib.Init.Logic.not); constr:(@Stdlib.ZArith.BinInt.Z.mod_pos_bound); constr:(@Stdlib.ZArith.BinInt.Z.mod_neg_bound); constr:(@Stdlib.omega.PreOmega.Z.div_0_r_ext); constr:(@Stdlib.omega.PreOmega.Z.mod_0_r_ext); constr:(@Corelib.Init.Logic.I); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.LiaTuning.zify_done); constr:(@Corelib.Init.Logic.eq_refl); constr:(@Corelib.Init.Datatypes.comparison); constr:(@Stdlib.ZArith.BinInt.Z.compare); constr:(@Corelib.Init.Datatypes.cons); constr:(@Stdlib.micromega.ZMicromega.ZArithProof); constr:(@Stdlib.micromega.ZMicromega.CutProof); constr:(@Stdlib.micromega.RingMicromega.PsatzAdd); constr:(@Stdlib.micromega.RingMicromega.PsatzIn); constr:(@Corelib.Init.Datatypes.S); constr:(@Corelib.Init.Datatypes.O); constr:(@Stdlib.micromega.ZMicromega.RatProof); constr:(@Stdlib.micromega.RingMicromega.PsatzMulE); constr:(@Stdlib.micromega.RingMicromega.PsatzC); constr:(@Stdlib.micromega.RingMicromega.PsatzMulC); constr:(@Stdlib.micromega.EnvRing.Pc); constr:(@Corelib.Numbers.BinNums.Zneg); constr:(@Stdlib.micromega.ZMicromega.DoneProof); constr:(@Corelib.Init.Datatypes.nil); constr:(@Corelib.Init.Datatypes.list); constr:(@Stdlib.micromega.VarMap.Branch); constr:(@Stdlib.micromega.VarMap.Elt); constr:(@Stdlib.micromega.VarMap.Empty); constr:(@Stdlib.micromega.VarMap.t); constr:(@Stdlib.micromega.Tauto.IMPL); constr:(@Stdlib.micromega.RingMicromega.Formula); constr:(@Stdlib.micromega.Tauto.eKind); constr:(@Corelib.Init.Datatypes.unit); constr:(@Stdlib.micromega.Tauto.isProp); constr:(@Stdlib.micromega.Tauto.AND); constr:(@Stdlib.micromega.Tauto.A); constr:(@Stdlib.micromega.RingMicromega.Build_Formula); constr:(@Stdlib.micromega.EnvRing.PEc); constr:(@Stdlib.micromega.RingMicromega.OpLe); constr:(@Stdlib.micromega.EnvRing.PEX); constr:(@Corelib.Init.Datatypes.tt); constr:(@Stdlib.micromega.RingMicromega.OpLt); constr:(@Corelib.Init.Datatypes.None); constr:(@Stdlib.micromega.Tauto.NOT); constr:(@Stdlib.micromega.RingMicromega.OpEq); constr:(@Stdlib.micromega.EnvRing.PEsub); constr:(@Stdlib.micromega.EnvRing.PEadd); constr:(@Stdlib.micromega.EnvRing.PEmul); constr:(@Stdlib.micromega.Tauto.X); constr:(@Stdlib.micromega.Tauto.BFormula); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker_sound); constr:(@Corelib.Init.Datatypes.bool); constr:(@Corelib.Init.Datatypes.true); constr:(@Stdlib.micromega.ZMicromega.ZTautoChecker); constr:(@Stdlib.micromega.VarMap.find); constr:(@Corelib.Init.Logic.False); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.aceil); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.AAPP_HI); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.addressable); constr:(@Stdlib.micromega.EnvRing.PEpow); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.SHAD); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shadow_of); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.Arr.u8arr); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.bsegs); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.sh); constr:(@stdpp.bitvector.definitions.bv); constr:(@Corelib.Lists.ListDef.repeat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Lib.TacX.b8); constr:(@Stdlib.ZArith.BinInt.Z.to_nat); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainLazy.SHOFF); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainIface.u8arr_constZ); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BoMainIfacePre.stack_shadow_zero); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.shadow_of_mult8); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.BSegs.ASHADOW_BASE); constr:(@OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsShadow.ASHADOW_BASE_val)|] [|@shi; @z; @Ha; @a; @__ff; @__varmap; @__wit; @__x1; @__x2; @__x3; @__x4; @__x5; @__p1; @__arith; @__sat8; @__sat7; @zh; @H0; @H6; @H12; @H16; @H15; @H14; @H13; @H11; @H10; @H9; @H8; @H7; @H5; @H4; @H3; @H2; @H1; @H; @__sat4; @__sat5; @__sat6; @g; @__p2; @l; @__sat9; @__sat10; @__x6; @Hz; @AC; @__sat1; @__sat0; @PD3; @PD2; @PD1; @Hlo; @lo; @Hh'; @HCEIL|] "#3K#K$i#P$H$I$G#q##$P#$#K$N#%#)#|#($T#'#&#*$,#.$2#;#+#5#/$>$Q#<#V#W#_#=#6$g#a#b#d#f#-$0$/#>$:#,$`$c#4#:#8#Q#S#`#c#e#g#h#i#j#k#l#m#s#0$'$7$=$<$@$S$[$\$Z$_#B$b#7#3$m#x#r#[#^#w#v#u$?$C$D$F$R$Y$]$^#1$a$e$d$h$i$k$l$j#A#H#G#F#J$o$n$p$q$r#N#Z#U#Y$E$L$K#O$4#n#o$J#]$A#R$%$V#X$O$5#p$6$9$M$U$W$3#y$$$&$($)$*$+$-$;$1$B#~$8$X#T#t$.#z$f#\#{#}$#U$8%$9$$:%$;+$<'$=*$>&$?&$@%$A%$B*$C$$D'$E%$F%$G&$H$$I%$J%$K%$L$$M&$N%$O&$P&$Q%$R'$S%$T%$U%$V%$W%$X%$Y%$Z&$[&$\%$]%#6$$^%$_)$`$$a'$b%$c)$d'$e%$f%$g&$h%USDH$S/$#$#$#$#$#L#VSE#S0$%$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3#05#)C>#USc70#&##H3A.B.#.#.#3#Q(##H#%+#dSdS0S1SFS5S6SGS7SHS8SISJSKSLSMSNSO#/s#$3?,1#+s#'#%&#.S/.#.#.#.#.#.#.#.#.#.#.#.#.#.#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3###s#C$s#H$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#$#3##s#]#%=#6s#_s#Q)C#G%%#%s#Q#VSEs#yS1USeS6VSf#S7XSgs#{%#S8MN#RH#.H%$#j#$C#VSPC#j##,#MS9)S)H%#(j#$C#VSPC#j##2#MSQ.S&H%#-j#$C#MS+1S9s#l#<s#m6Hs#i0H#)C#s#xj#%C#Rs#xs#s+Gs#y#Gs#u+Gs#uk##$#k##&##Gs#~Ss$#s#zJj##O#j#&%##Gs#|k##O#k#&(#Hs$.s#z#Gs$/#Gs#|6s$1s#}#G#k##%#k##'#Ts$Hs$%#Gs$I>s$Js$'#G#k##+#k##&#1&s$+H#s$,#G$6%s$.#G#k##2#k##&#?s$Us$2)Cs$3GUSR#1s$506s$Ys$6,$#)Cs$[#k##'#@s$]s$:+Gs$;#G(+)s$=%$#k##&#As$cs$@+s$AG+s$B.#/G%$#k##&#Bs$is$F)CBGk##7#Cs$ls$I)C6s$mk##:#Ds$os$Lm#S%#?s$^s$N>s$_s$O1s$P#,#s#2)Cs$b#k##A#@s$ds$T+s#6s$U%s#6#k##>#As$hs$X+s$Ys#:#s#;G%$#k##=#Bs$ms$])C1Gk##s#.#Cs$ps$`)Cs#Bs$qk##s#1#Ds$ss$cm#S%#?s#<s$e>s#=s$f1s$g#,#s#<)Cs#@#k##s#8#@s#Bs$k+s#@s$l%s#@#k##s#5#As#Fs$o+s$ps#D#s#EG%$#k##s#4#Bs#Ks$t)C1Gk##s#E#Cs#Ns$w)Cs#Ls#Ok##s#H#Ds#Qs$zm#S%#VS:Gs$|NS;#m##s#EUR#I$US*%VS2HJj#'s#n#k#'s#os#kVS:Gs%4NS;#m##s#wUS<#7SS7#7#7#7#5C#5CSS*C$#3s$]VS=C#8C#&VS=Cs%87*7#7#5C#8C'#USTs%[VSUC#5C)EC$#5C48C-#5C78C/#*C%#*C(#*C-#*C4#J#S,<9#USTS/VSUC#EC#>*C#>5C8EC&/*CB#*C5#*C&#5Cs#*8C@#8CAs#&*C$#J#S,<(#<.#UShS'FS'$#FS'5#USVS'GCPUSiC/C$P#/C#M$GCR/C&S##/C%J#USjCUSkC9CG4Cs&8'C$L#(&FDDE#I9Cs%m'C&S-#()FDDE#I-*FDDE&#USlD'C'Q+(-FDDE#IZSW.FDDE#4CS/9Cs&+:C$#4Cs&D;C.#2C#2'C&Q#(6FDDE#I&7FDDE+.#4Cs%y'C8L#(:FDDE#I'C%S-6(<FDDE#I-=FDDE%#4Cs&$;C:#2C#*'C4Q#(BFDDE#I&s##FDDE7:#9Cs%X;C)@'C$L#(s#'FDDE#IKs#(FDDES$-s#)FDDE$#:C;s#(:C(='C$Q#(s#-FDDE#I&s#.FDDE's#%#&s#/FDDE.s#&#&s#0FDDE5s#'#&s#1FDDE<s#(#&s#2FDDEs#*s#)#VSms#3ENSXSYVSnHM)SX#SYm$%#WSoCGJXSZHM$#l#(*)#l#)s#=s#<#l#*s#Fs#E#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K##GJ+Js&N%$#k##s${S[0Ms&b1s&RN,#S#)C%#k##'##GP+Ps&W%$#,)S$)CR#k##-#1Ns&\#s&+#%#S>0Ps&p0#N1S$s&a0#s&s)C%#k##(#k##,#k##0#k##4#k##;#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K##s%Fs&#_H#s%#s%<s%Ks%Qs'7PS*RS(S\l#1s#'%#l#2s$Hs%_#l#3s$Ns$M#l#4S#O#l#5s$Rs%9#l#6s$Ts$~#l#7s$Vs$h#0s',s%Y0s%Ps'.)C$#m#&#l#8s$_s$`#l#9s$ds$b#l#:s$hs$f#l#;s$ns$j#l#7s$ss$p#l#<s$zs$u#l#=s$|s$}#l#>s%%s%##l#?s%)s%'#l#@s%/s%+#l#6s%4s%1#l#As%;s%6#l#Bs%=s%>#l#Cs%Bs%@#l#Ds%Fs%D#l#Es%Ms%H#l#5s%Ts%O#l#Fs%]s%V#l#Gs%ds%_#l#Hs%ls%g#l#Is%ts%n#l#3s%ys%v#l#2s&'s%~#)C=s'Dm#$#USDS+OCs'Js&,$#S&US?S+)C#s'Im#%#US?Sp##H#HS+%$##S+s'G#s'HSq%$#0s'JH3s'n6$#)C#GWS]s&OH&%$#%)#%-#j#JC#US?SQ#HH%#2%#(j#%C##s'`s'`#s'aS&%$##S&s'[#s'\s'\%$#0s'^s'f6#6)C#GWS]s&bs'i%%$#%(#Hs'ms'_#Gs'n#Gs&nk##s&D#k##%#?s'rs'd>s'ss'e1s'f#,#s&t)Cs'v#k##s&7#@s'xs'j+s&xs'k%-#k##s&4#As'|s'n+s'os&|#s&}G%$#k##s&3#Bs(%s's)C1Gk##s&D#Cs((s'v)Cs'(s()k##s&G#Ds(+s'ym#S%#VS9HJj#'s&g#Is%TGCM/C#Js$|'Cs$gLs$t(s$wFDDE#IKs$xFDDER-s$yFDDE$#'Cs$kLs$k(s${FDDE#I-s$|FDDE#'&s$}FDDE&s$t#l#(#s$Ms$Gl#),s%$#l#*s%0s%-#j#+C#j#,C#j#0K#0Hs(C##J%#M0Js(F####$M%$#k##'#k#+C#k#,C#k#0K##S.s(BXH#S.s(LS(l#10%#l#IAs'-#l#Hs##s%w#l#4JO#l#5s%~s#5##s(QS^%s#P#m#%#l#Bs#+s#,#l#Cs#0s#.#l#Ds#4s#2#l#Es#:s#6#l#5s#?s#<#l#Fs#Fs#A#l#Gs#Ls#H#l#Hs'6s'3#l#Is'@s';#GCJKs%GFDDES#9Cs(]Ls(ZWS@C$#'Cs%>L#(s%LFDDE#I-s%MFDDE(#'C&L&(s%OFDDE#I-s%PFDDE&#&s%QFDDE&s%H#l#(#s$}s$wl#)/s%T#l#*s%`s%]#j#+C#j#0K#%Js(e#Js(g%#s#jk##%#k#+C#k#0K##s(tS.WH#S.S(l#1+%#l#Is#Ks'W#l#Hs#Ms&E#l#4JO#l#5s&Ls#_##S^s(s%#s#vm#%#l#Bs#Us#V#l#Cs#Zs#X#l#Ds#^s#\#l#Es#ds#`#l#5s#is#f#l#Fs#ps#k#l#Gs#vs#r#l#Hs'`s']#l#Is'js'e#Hs$#s$6#Gs$$#Gs$8#Gs$%k##$#k##&#?s$)s$<)Cs$=GUSR#>s$,s$?1s$@#,#s$-)Cs$/#k##'#@s$1s$D+Gs$E+s$2s$F%0#k##%#As$6s$I+s$JG+s$Ks$7#s$8G%$#k##&#Bs$<s$O)C3Gk##6#Cs$?s$R)Cs$?s$@k##9#Ds$Bs$Um#S%#VS:Gs$WNS;#m##6I#VS*HJj#'s(/#US3s&xECs&Ws&T*Cs&Ts&r*Cs&X#*C%#*Cs&hs&f*Cs&Y#*Cs&n#*Cs&Vs&xJ#S,<%#<)#FS'#s&S/Cs&LMs&OGCS#/C$P#/Cs&QPs&R/C$J#4Cs*$.s*%4C#;Cs&K#$s)W4C#2C%#'C)Q#(s&UFDDE#I&s&VFDDEs&Js&M#9Cs$y'Cs&KS-#(s&YFDDE#I-s&ZFDDEs&4#'C&Qs&Z(s&\FDDE#IZSWs&]FDDE#:C3s&P:Cs#s#;C+s&P2C#s&T'C%Q#(s&cFDDE#I&s&dFDDE)s&[#'Cs&dL((s&fFDDE#I'Cs&fL2(s&hFDDE#I'Cs&hLs&\(s&jFDDE#I&s&kFDDE%s&b#&s&lFDDE(s&c#'C=Qs&l(s&nFDDE#I'Cs&MLs#$(s&pFDDE#I9Cs)/'Cs#'L#(s&sFDDE#I-s&tFDDE&#'Cs&hQs&t(s&vFDDE#I&s&wFDDE%s&n#&s&xFDDE,s&o#&s&yFDDE/s&p#&s&zFDDE8s&q#&s&{FDDEs##s&r#&s&|FDDEs#(s&s#l#(#s&Ls&Fl#)s#4s'##l#*s#:s',#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#1s*4P,#S#)CM#k##s&E#+Js%P%N#k##s#sS[0Rs*L0s*A#1s%UN,#S#)C%#k##(##G'k##s$$s&Jk##$#)CNG#s)oN#Ns)V%$#k###&k##'#k##)#k##-#k##5#k##8#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K#`Hs$5s%Ms$/s)as*bs%XS&RSAS3SBS(l#1s#$$#l#3s#os)C#l#Is#qs(1#l#4MO#l#5s#us$,#l#6s(9s%L#m##s%^l#=s%@s%A#l#>s%Es%C#l#?s%Is%G#l#@s%Os%K#l#6s%Ts%Q#l#As%[s%V#l#Bs$&s$'#l#Cs$+s$)#l#Ds$/s$-#l#Es$6s$1#l#5s$<s$8#l#Fs$Es$>#l#Gs%gs%c#l#Hs$Ms$H#l#Is)Rs)O#l#3s)\s)W#USrs%qWSss)ss*z#'Cs'WLs#Q(s'eFDDE#I-s'fFDDEs$}#:Cs${s'X'Cs'gL#(s'iFDDE#I&s'jFDDE&s'a#l#(#s':s'4l#)s%(s'm#l#*s'ys'v#j#+C#j#0K##Hs*.%J#0s+%s%I#G#k##%#k#+C#k#0K#WHs*Ns+3S_l#1+$#l#Is%ds)p#l#Hs%fs(^#l#4JO#l#5s(es%x#m##s$jl#Bs%ls%m#l#Cs%qs%o#l#Ds%us%s#l#Es%{s%w#l#5s&$s%}#l#Fs&+s&&#l#Gs&1s&-#l#Hs)ws)t#l#Is*%s)|##Gs+B6s+Cs&N)C#GUSts+EPS4s*?#s#+%%#'Cs'kLs($(s(2FDDE#I-s(3FDDE#s%J'Cs(3Ls(%(s(5FDDE#I&s(6FDDE%s(-#l#(#s'bs'\l#)s%Ps(9#l#*s(Es(B#j#+C#j#0K##s*pH%#J#Gs%qk##$#k#+C#k#0K#WHs*[s+ZS_l#1*$#l#Is&/s*;#l#Hs&1s))#l#4JO#l#5s)0s&C#m##?l#Bs&7s&8#l#Cs&<s&:#l#Ds&@s&>#l#Es&Fs&B#l#5s&Ks&H#l#Fs&Rs&M#l#Gs&Xs&T#l#Hs*Bs*?#l#Is*Ls*G#Hs+is&t#Gs#)k##s%@#k##s#,#?s+ms&x>s+ns&y1s&z#,#s#/)Cs+q#k##s%A#@s+ss&~+s#3s'#%-#k##s%>#As+ws'&+s''s#7#s#8G%$#k##s%>#Bs+|s'+)C1Gk##s%N#Cs,#s'.)Cs#?s,$k##s%Q#Ds,&s'1m#S%#ECs),s)95Cs)LECs).#*Cs):#*Cs)K#*C'#*Cs);s)**Cs)2#*Cs)1#<#s%4<'#FS'#s)('Cs$yQs$v(s(zFDDE#I&s({FDDEs$|s(r#'Cs({Ls$|(s(}FDDE#I&s(~FDDE#s(us$qKs)#FDDES)-s)$FDDEs$n#&s)%FDDE#s(xs$i&s)&FDDEs$rs(y#&s)'FDDE's(z#&s)(FDDE+s({#&s))FDDEs%-s(|#&s)*FDDEs%2s(}#l#(#s(Vs(Pl#)s%>s)-#l#*3s)6#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#j#KK#)Cs$bs$_k##s$d##Gs$dk###s$^%s$\S&k###s$^k##s$_#k##&#k##)#k##s$m#k##s$p#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K#k#KK#aHs+`s#Rs'Js#Ns+^s,_s#yS&RSAS*SBS(l#16$#l#3s%ls+@#l#Is%ns*.#l#4MO#l#5s%rs#L#l#6s*6s'I#m##s$#l#=s'=s'>#l#>s'Bs'@#l#?s'Fs'D#l#@s'Ls'H#l#6s'Qs'N#l#As'Xs'S#l#Bs#Gs#H#l#Cs#Ls#J#l#Ds#Ps#N#l#Es#Vs#R#l#5s#[s#X#l#Fs#bs#]#l#Gs#gs#d#l#Hs'es'a#l#Is+Os+L#l#3s+Ys+T#3s,H,Hs#gPS4s+q#s$]j#%C#Ls-9USu#USV#USvGUSws&LWSx&$#,S`s#pPS4s+z#Hj#L(#Ts-'s(2#Gs#tk##s&Z#k##s$F#VSAHJj#'s+f#US*s*S/Cs']Ms)z/C#Js){-s)uFDDEs%cs'[9C92C#s)j'Cs)wL#(s)yFDDE#I&s)zFDDE's)q#&s){FDDEs#[s)r#l#(#s)Ks)El#)+s)~#l#*s*.s*+#j#+C#j#,C#j#0K##GMk##s&o#k##s$H##s,]M%#S#,s#*M#G#k##%#k##(#k#+C#k#,C#k#0K#YHs,Ks-Js$9SCS(l#10$#l#I@s,+#l#HBs*u#l#4MO#l#5s&]s$7#l#6s*}s(4#,s#8s$@#G#m#%#l#=s(*s(+#l#>s(/s(-#l#?s(3s(1#l#@s(9s(5#l#6s(>s(;#l#As(Es(@#l#Bs$4s$5#l#Cs$9s$7#l#Ds$=s$;#l#Es$Cs$?#l#5s$Hs$E#l#Fs$Os$J#l#Gs(Qs(M#l#Hs,;s,8#l#Is,Es,@#l#3s#=s#:##Gs#Am#$#Ts(]s(p#Gs'4k##s'<#k##s'>#-s*RFDDEs(8s&=&s*SFDDE#s*Js&G&s*TFDDEs&Fs*K#l#(#s*$s)zl#)s#@s*W#l#*s*cs*`#j#+C#j#,C#j#0K#k##s%Fs#6#Ms,v%S##k###s#:k##&#k#+C#k#,C#k#0K#YHs-:s-{s'HS3S(l#1,$#l#3s',s,\#l#Is'.s+J#l#4MO#l#5s'2s'E#l#6s+Rs(e#m##=l#=s(Ys(Z#l#>s(^s(\#l#?s(bs(`#l#@s(hs(d#l#6s(ms(j#l#As(ts(o#l#Bs'?s'@#l#Cs'Ds'B#l#Ds'Hs'F#l#Es'Os'J#l#5s'Us'Q#l#Fs'^s'W#l#Gs)$s(|#l#Hs#,s#)#l#Is,ks,h#l#3s,us,p#3s.NRs.5##G$Qs.7%+G#k##%#k##s,{#Ss.;)Jj##O#j#&s,y##G)k##O#k#&s,|#US*s'SVSBHJj#'s-##k#'s-$(US(s+mVSyHJj#'s-'#US\s+pVS=Cs)V8C#s+j*Cs+M#*Cs+]#*Cs+R#*Cs+a#J#S,FS'#s+G/Cs+CMs+B/Cs+AS#s+D/C#Ps+E/C%J#$s.T4C#'Cs+AL#(s+CFDDE#I-s+DFDDE#s*z4Cs.Y:C#s+8:Cs([#;Cs'Os+F2C#*'C%Q#(s+KFDDE#I&s+LFDDEs'Ms+C#'Cs+LLs'\(s+NFDDE#I-s+OFDDE#s%.;Cs'Ws+C2C#s'`'C.Q#(s+SFDDE#I&s+TFDDEs'Us+K#'Cs+3L2(s+VFDDE#I'C4Ls'D(s+XFDDE#I-s+YFDDE%#2Cs$As+XWS@Cs(qs/-'C$L#(s+]FDDE#I&s+^FDDE's+U#&s+_FDDE-s+V#&s+`FDDE3s+W#&s+aFDDE7s+X#&s+bFDDE@s+Y#l#(#s+2s+,l#)s#'s+e#l#*s#,s+n#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#j#KK##GR%#P1s*5S#,#N)Cs'A#k##s'D#%s+)S)0Ns/31s*;R,#S$)C%#k##s'J#,s$xP,#N##s#[k##s'A#k##'#k##-#k##/#k##4#k#+C#k#,C#k#-C#k#.C#k#/C#k#0K#k#KK#`Hs&-s(fs*:s&^s/Ds(ms&3S)SCS$S<Szl#1?$#l#Ms#Ys.%#l#2s#[s,o#l#4NO#l#Hs#_s#k#l#Gs#bs#a#l#4S#O#l#5s#fs&4#l#6s([s(n#l#7s,{s*2#,s$\s(x##s#tm#%#l#8s*(s*)#l#9s*-s*+#l#:s*1s*/#l#;s*7s*3#l#7s*<s*9#l#<s*Cs*>#l#=s(js(k#l#>s(os(m#l#?s(ss(q#l#@s(zs(u#l#6s)$s(|#l#As)-s)&#l#Bs&8s&9#l#Cs&=s&;#l#Ds&As&?#l#Es&Gs&C#l#5s&Ls&I#l#Fs&Ss&N#l#Gs$&s$##l#Hs$/s$*#l#Is*Ws*S#l#3s$_s$\#l#2s.Bs.?#l#Ms.Ls.G#l#Ns%Ds%A#,s%Hs)8##s$4m#%##s%KH+H&%$#$s/l$#3#Rs/q##G$Qs/s%+G#k##%#k##s.[#Ss/w)Jj##O#j#&s.Y##G)k##O#k#&s.\#VS.HJj#'s.^#US2s-Kk#'s.`(8Cs$:s-4*C#s$:*Cs-,#*Cs-;#*Cs)6#*Cs-A#J#S,FS'#s-#/Cs,|Ns,{/Cs,|M#GCN/C#Ns,~/Cs$=N#/C&J#4Cs01'Cs,zL#(s,|FDDE#I-s,}FDDE#s&\;Cs))s)12C#''Cs$;Q#(s-%FDDE#I&s-&FDDEs)'s,y#Ks-'FDDES>-s-(FDDEs$C#2Cs$7s$F'Cs$BQ#(s-+FDDE#I&s-,FDDEs)-s-##'Cs%pLs-+(s-.FDDE#I2Cs%rs)>'Cs-.S-#(s-1FDDE#I-s-2FDDE&#Ls#7WS@Cs*J#2Cs%y#'Cs-4S-#(s-7FDDE#I-s-8FDDE,#&s-9FDDEs$>s-0#&s-:FDDE*s-1#&s-;FDDE1s-2#&s-<FDDE6s-3#&s-=FDDE9s-4#&s->FDDE?s-5#l#(#s,js,dl#)s#%s-A#l#*s#,s-J#j#+C#j#,C#j#-C#j#.C#j#/C#j#OC#j#0K#j#KK#%s,\N1s+mP,#S$)Cs(y#k##s(|##GN%#S>,s$:S))Cs$<#k##s)%#,s&SR##P,$S$+P#%%##s01S$#S$s/t%$#,s&[N##S$,s&]s#^+S$#%%#k##(#k##,#k##2#k##6#k##9#k##>#k#+C#k#,C#k#-C#k#.C#k#/C#k#OC#k#0K#k#KK#bHs'ps*Ms+}s(Es*Ts1+S{s'vS)SCS$S<S|S}l#1s#)$#l#Ms%@s#o#l#2s%Bs#e#l#4NO#l#3s#hs/k#l#Is#js.Y#l#4S#O#l#5s%Ms'w#l#6s*Bs*U#l#7s.bs+u##s&CS2+S2?%$#m#&#l#8s+ls+m#l#9s+qs+o#l#:s+us+s#l#;s+{s+w#l#7s,$s+}#l#<s,+s,&#l#=s*Rs*S#l#>s*Ws*U#l#?s*[s*Y#l#@s*bs*]#l#6s*hs*d#l#As*qs*j#l#Bs'|s'}#l#Cs(%s(##l#Ds()s('#l#Es(/s(+#l#5s(4s(1#l#Fs(;s(6#l#Gs,=s,9#l#Hs&Es&B#l#Is0(s0%#l#3s02s0-#l#2s$2s$/#l#Ms$;s$6#l#Ns',s')##s'0J,S`s$<+J#%%#m#'#fS~S0S1SFS5S6SGS7SHS8SISJSKSLSMSNSOJ#j#Ps$G#j#%C#_T#S0S1S5s0Ss'8s+(Gs&Ts&'s$L#URs//Is/'XSZHMs-ps-ll#(s);s-r#l#)s+`s.I#l#*s.Us.R#j#+C#j#0K#l#1#s)4s)3l#I*s0D#l#Hs,:s/2#l#4JO#l#5.s,L#l#BS%s,@#l#Cs,Ds,B#l#Ds,Hs,F#l#Es,Ns,J#l#5s,Ss,P#l#Fs,Zs,U#l#Gs,`s,\#l#Hs0Js0G#l#Is0Ts0O#Is+&US3s/=l#(s*>s.+8l#)s*os.^#l#*s*us.g#j#+C#j#,C#j#-C#j#.C#j#/C#j#0K#l#1#s)zs)yl#3-s0]#l#Is+/s/K#l#4MO#l#51s+F#l#6s#(s,f#l#=S%s,Z#l#>s,^s,\#l#?s,bs,`#l#@s,hs,d#l#6s,ms,j#l#As,ts,o#l#BS%s+@#l#Cs+Ds+B#l#Ds+Hs+F#l#Es+Os+J#l#5s+Us+Q#l#Fs+^s+W#l#Gs-$s,|#l#Hs+fs+a#l#Is0ks0h#l#3s0us0p#WT$s-.s#$#Os'us'rs'os#;s)x#PS4s11s'Fs)ym#$#OCs'~s'{#T%T&m##s)S=s)Vs)Ts(%#=s)Ys)Ts)3#m##s)~=s+qs*#s)\#m##s-5=s-7s-6s*'#=s-;s-6s+v#=s-?s-6s,E#%s-?s-R%#s-9%s-B#m#&#OCs2Hs-G#s-KHXSaCs-Ms-L#l#Qs-^s-_#UJs/q'Cs*~Ls,I(s/6FDDE#Il#(#s.bs.\l#)s/?s/9#l#*s/Es/B#l#1#s1:Hl#R)s12#l#Ss1.s1+#l#Rs18s13#=s1?s1>-#XSaCs1As2N#j#Ts1V#j#Us1Y#V#JHj##s1Y#j##s1\#YSbs1]s1[s1J#Hj#Fs1[#j#Vs2N#V#JHj##s1^#j##s2Q#YSbs2Rs1`s1U#Hl#Fs2Xs1`#j#Ws2Z#j#XC#j#Ys2h#j#ZT'##"). Qed.
End AT_MAIN.
