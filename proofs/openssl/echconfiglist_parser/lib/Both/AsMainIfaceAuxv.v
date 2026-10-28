(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsPrintfFirst AsDrvDefs AsMainPre AsAuxv.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import CatExec RefLayout ArgvEnv FileSim MuslStrlen.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsHSTab AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface AsMainIfacePre. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
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
    unfold GHZ, Xof in B, Bg, B13;
    cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_b24 ps_a1 ps_a2 ps_a3 ps_g1 ps_g2 ps_g3 ps_g4 ps_granted] in B, Bg, B13;
    repeat (apply Forall_cons_iff in B as [? B]);
    (let BG4 := fresh "BG4" in let BG3 := fresh "BG3" in let BG2 := fresh "BG2" in let BG1 := fresh "BG1" in
     apply Forall_cons_iff in B13 as [BG4 B13]; apply Forall_cons_iff in B13 as [BG3 B13]; apply Forall_cons_iff in B13 as [BG2 B13];
     apply Forall_cons_iff in B13 as [BG1 B13]; apply Forall_inv in B13);
    cbn [fst snd] in *;
    pose proof (u64_range brk0) as ?Hb0; pose proof (u64_range sp0) as ?Hs0;
    pose proof (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL) as ?HRIv.
  Ltac zlistsI :=
    unfold pm_vmem in *;
    unfold PM_LAZY, PM_S, PM_ZR, PM_NOACC, PM_MAPS, PM_REM, VISZ, VISZ0, GHZ, SW;
    rewrite ?(RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl) by assumption;
    unfold Xof in *; cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_b24 ps_a1 ps_a2 ps_a3 ps_g1 ps_g2 ps_g3 ps_g4 ps_granted map app fst snd] in *.

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
  #[local] Notation kp_b24 := (AsMainIface.kp_b24 h E) (only parsing).
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
  #[local] Notation vr_b24 := (AsMainIface.vr_b24 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
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
  #[local] Notation MR := (Mr ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model FULL).
  #[local] Notation HID := (hid ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model).
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation envc := (Z.of_nat (length (in_envp inp))).
  #[local] Notation BSB := (build_stack_bytes APH sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw).
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.
  #[local] Notation kword_main := (AsMainIfacePre.kword_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  (* [comment removed for export] *)
  Definition isSomeA {T} (o : option T) : bool := match o with Some _ => true | None => false end.
  Lemma no_wrapA : forall e, isSomeA (lin_ofxB (mkbc (kn ch)) e) = true -> uE E e = lden E (lin_of e).
  Proof.
    intros e H. destruct (lin_ofxB (mkbc (kn ch)) e) as [l|] eqn:L; [|discriminate].
    rewrite lin_ofxB_eqf in L. pose proof (lin_ofx_sound _ _ _ _ KNF _ _ L) as S.
    unfold lin_ofx in L. destruct (lin_nowrapR (kn ch) e); [|discriminate]. injection L as <-. exact S.
  Qed.
  Lemma W_factsA : 0 <= vE E 4 /\ 8 * vE E 4 = Z.of_nat (length BSB) - 16 - (8 * argc + 8 * envc + 184) /\ vE E 4 <= 280000.
  Proof.
    pose proof (AsanInit.W_range APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vav Vev) as (W1 & W2 & W3).
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 4%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. rewrite u_of_Z by lia. repeat split; lia.
  Qed.
  Lemma layA :
    8 * argc + 8 * envc + 200 <= Z.of_nat (length BSB) /\ sp0z + Z.of_nat (length BSB) <= 2 ^ 47 /\ 1 <= argc <= 1024 /\ 0 <= envc <= 256
    /\ 0x7fff80000000 <= sp0z <= 0x800000000000.
  Proof.
    pose proof (AsanInit.bsb_ge APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp)) as [G _].
    pose proof (AsanInit.usp_fit APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vfit) as UF.
    pose proof (AsanInit.len_av APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vav) as LA.
    pose proof (AsanInit.len_ev APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vev) as LE.
    pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition ALIBC_AUXV : Z := 0xc01f28.
  Definition auxv_keys : list Z := [3; 4; 5; 16; 6; 11; 12; 23; 25; 0].
  Definition auxv_vals : list expr :=
    [ELit (ph_addr_z ASAN_H); ELit (ph_ent_z ASAN_H); ELit (ph_num_z ASAN_H); EVar V_HW; ELit 4096; EVar V_UID; EVar V_UID; ELit 0; e_atrandom; ELit 0].
  Definition ten : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9].
  (* [comment removed for export] *)
  Definition auxv_check : bool :=
    all_holes (fun g cls ch =>
      forallb (fun i => has_fact (kn ch) (KWord (SA (fst e_auxb) (snd e_auxb + 16 * i)) 8 (ELit (nth (Z.to_nat i) auxv_keys 0)))
                        && has_fact (kn ch) (KWord (SA (fst e_auxb) (snd e_auxb + (16 * i + 8))) 8 (nth (Z.to_nat i) auxv_vals (ELit 0)))) ten
      && isSomeA (lin_ofxB (mkbc (kn ch)) (fst e_auxb)) && isSomeA (lin_ofxB (mkbc (kn ch)) e_auxv)).
  Lemma auxv_check_ok : auxv_check = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma libc_auxv_check : kword_check_w w_all (CAbs, ALIBC_AUXV) 8 e_auxv = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_auxb : lin_of (fst e_auxb) = (0, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (4096, EVar 6); (16, EVar 10)]) /\ snd e_auxb = 24.
  Proof. vm_compute. split; reflexivity. Qed.
  Lemma lin_e_auxv : lin_of e_auxv = (24, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (4096, EVar 6); (16, EVar 10)]).
  Proof. vm_compute. reflexivity. Qed.

  #[local] Notation av := (sp0z + 8 * argc + 8 * envc + 24).

  Lemma u_auxb : uE E (fst e_auxb) = sp0z + 8 * argc + 8 * envc /\ snd e_auxb = 24 /\ uE E e_auxv = av.
  Proof.
    pose proof auxv_check_ok as H0. unfold auxv_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply andb_prop in H as [H N2]. apply andb_prop in H as [_ N1].
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & SP & _ & _ & V1 & V2 & _).
    rewrite (no_wrapA _ N1), (no_wrapA _ N2). pose proof lin_e_auxb as [LA SA]. rewrite LA, SA, lin_e_auxv.
    unfold lden. cbn [fst snd tden]. rewrite !uE_var. rewrite V1, V2. repeat split; lia.
  Qed.

  Lemma auxv_lay : sp0z + 32 <= av /\ av + 176 <= 2 ^ 47 /\ av mod 8 = 0 /\ 0x7fff80000000 <= sp0z.
  Proof.
    pose proof layA as (G & UF & LA & LE & VS). pose proof Vsp as [_ [_ AL]].
    repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hid_auxv : forall z, av <= z < av + 160 -> HID (Z_to_bv 64 z) = false.
  Proof.
    intros z Hz. pose proof layA as (G & UF & LA & LE & VS). pose proof Vsp as Vsp'. destruct Vsp' as [Vlo [Vhi _]]. unfold sp_window_lo, sp_window_hi in Vlo, Vhi.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TOPm & _).
    pose proof W_factsA as (W1 & W2 & W3).
    unfold hid. apply orb_false_iff. split.
    - unfold argH0. apply andb_false_iff. left. unfold argB0. rewrite u_of_Z by lia.
      apply orb_false_iff. split; apply andb_false_iff; [right; apply Z.ltb_ge; lia | left; apply Z.leb_gt; lia].
    - apply negb_false_iff. unfold vis. rewrite u_of_Z by lia.
      replace (TOP model <=? z) with true by (symmetry; apply Z.leb_le; lia). destruct (in_hull ASAN_H z); reflexivity.
  Qed.

  Lemma wa_wordA : forall x : word, wa (bv_unsigned x) = x.
  Proof. intros x. unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

  Lemma auxv_slot_main : forall (off : Z) (v : expr),
    has_fact (kn ch) (KWord (SA (fst e_auxb) (snd e_auxb + off)) 8 v) = true -> 0 <= off -> off + 8 <= 160 ->
    rdn ASEGS VM (Z_to_bv 64 (av + off)) 8 = Some (word_to_le_bytes 8 (edenot E v)).
  Proof.
    intros off v HF Ho1 Ho2. pose proof layA as (G & UF & LA & LE & VS). pose proof pd_facts as PD.
    pose proof u_auxb as (UB & SB & _).
    unfold has_fact in HF. apply existsb_exists in HF as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. cbn [kentry_ok] in KO. destruct KO as (_ & FL & RD).
    assert (Ha : adenot E (SA (fst e_auxb) (snd e_auxb + off)) = Z_to_bv 64 (av + off)).
    { apply bv_eq. rewrite (flat_u E _ _ FL). unfold estart. cbn [a_base a_off]. fold (uE E (fst e_auxb)). rewrite UB, SB, u_of_Z; [lia | lia]. }
    rewrite Ha in RD.
    assert (RF : rdn ASEGS FULL (Z_to_bv 64 (av + off)) 8 = Some (word_to_le_bytes 8 (edenot E v))).
    { apply (rdn_Mr_full _ _ _ RD). intros i Hi. rewrite u_of_Z by lia. apply hid_auxv. lia. }
    rewrite <- RF. apply rdn_ext; [rewrite u_of_Z by lia; lia|]. intros x Hx. rewrite u_of_Z in Hx by lia.
    rewrite <- (wa_wordA x). apply vm_stack. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem auxv_cell_main : rdn ASEGS VM (Z_to_bv 64 ALIBC_AUXV) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 av)).
  Proof.
    pose proof u_auxb as (_ & _ & UV). pose proof auxv_lay as (L1 & L2 & _ & L4).
    pose proof (kword_main w_all (CAbs, ALIBC_AUXV) 8 e_auxv libc_auxv_check (world_ok_all _ _) ltac:(lia)) as W.
    revert W. pmc_simpl. rewrite Z.add_0_l. intros W. change AsanUbsan.M.loaded_segments with ASEGS.
    unfold ALIBC_AUXV in *. rewrite (W ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)). do 2 f_equal. apply bv_eq.
    change (bv_unsigned (edenot E e_auxv)) with (uE E e_auxv). rewrite UV, u_of_Z; [reflexivity | lia].
  Qed.
  (* [comment removed for export] *)
  Theorem auxv_key_main : forall i, 0 <= i < 10 ->
    rdn ASEGS VM (Z_to_bv 64 (av + 16 * i)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat i) auxv_keys 0))).
  Proof.
    intros i Hi. pose proof auxv_check_ok as H0. unfold auxv_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. rewrite forallb_forall in H.
    assert (Hin : In i ten) by (unfold ten; cbn [In]; lia).
    specialize (H i Hin). apply andb_prop in H as [HK _].
    assert (Hk : 0 <= nth (Z.to_nat i) auxv_keys 0 < 2 ^ 64).
    { unfold auxv_keys. destruct (Z.to_nat i) as [|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]; cbn [nth]; try lia. destruct n; cbn; lia. }
    rewrite (auxv_slot_main (16 * i) _ HK) by lia.
    do 2 f_equal.   (* [comment removed for export] *)
    all: apply bv_eq; cbn [edenot]; rewrite u_lit64a, u_of_Z by lia; apply Z.mod_small; exact Hk.
  Qed.
  (* [comment removed for export] *)
  Theorem auxv_val_main : forall i, 0 <= i < 10 ->
    exists w : word, rdn ASEGS VM (Z_to_bv 64 (av + 16 * i + 8)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros i Hi. pose proof auxv_check_ok as H0. unfold auxv_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. rewrite forallb_forall in H.
    assert (Hin : In i ten) by (unfold ten; cbn [In]; lia).
    specialize (H i Hin). apply andb_prop in H as [_ HV].
    exists (edenot E (nth (Z.to_nat i) auxv_vals (ELit 0))).
    replace (av + 16 * i + 8) with (av + (16 * i + 8)) by lia.
    exact (auxv_slot_main (16 * i + 8) _ HV ltac:(lia) ltac:(lia)).
  Qed.
  (* [comment removed for export] *)
  Theorem auxv_lay_main : sp0z + 32 <= av /\ av + 176 <= 2 ^ 47 /\ av mod 8 = 0 /\ 0x7fff80000000 <= sp0z.
  Proof. exact auxv_lay. Qed.

  (* [comment removed for export] *)
  Lemma rdnA_S : forall m (a : word) n bs,
    rdn ASEGS m a (S n) = Some bs -> exists b r, bs = b :: r /\ mrd asegs m a = Some b /\ rdn ASEGS m (a + 1)%bv n = Some r.
  Proof.
    intros m a n bs HR. rewrite asegs_ASEGS. change (rdn ASEGS) with (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn ASEGS) in HR |- *.
    rewrite rdn_unfold in HR. destruct (mrd ASEGS m a) as [b|]; [|discriminate].
    destruct (OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib.PropExec.rdn ASEGS m (a + 1)%bv n) as [r|]; [|discriminate].
    injection HR as <-. exists b, r. auto.
  Qed.
  Lemma rdnA_bytes_at : forall bs m (a : Z),
    rdn ASEGS m (Z_to_bv 64 a) (length bs) = Some bs -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at asegs m a bs.
  Proof.
    induction bs as [|b bs IH]; intros m a HR Ha Hn.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - cbn [length] in HR, Hn. destruct (rdnA_S m _ _ _ HR) as (b' & r & E0 & Hm & Hr). injection E0 as <- <-.
      split; [lia|]. split; [cbn [length]; lia|].
      intros i Hi. destruct i as [|i].
      + cbn. rewrite Z.add_0_r. change (wa a) with (Z_to_bv 64 a). exact Hm.
      + cbn [nth_error]. destruct (Z.eq_dec (a + 1) (2 ^ 64)) as [Heq|Hne]. { cbn [length] in Hi. lia. }
        assert (IHr := IH m (a + 1)).
        assert (Ea : (Z_to_bv 64 a + 1)%bv = Z_to_bv 64 (a + 1)).
        { apply bv_eq. rewrite u_add1 by (rewrite u_small by lia; lia). rewrite !u_small by lia. reflexivity. }
        rewrite Ea in Hr. specialize (IHr Hr ltac:(lia) ltac:(cbn [length] in Hi |- *; lia)).
        destruct IHr as (_ & _ & IH3). rewrite <- (IH3 i) by (cbn [length] in Hi; lia). f_equal. f_equal. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma bytes_at_words : forall ws m (a : Z),
    (forall i w, nth_error ws i = Some w -> rdn ASEGS m (Z_to_bv 64 (a + 8 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 w)) ->
    0 <= a -> a + 8 * Z.of_nat (length ws) <= 2 ^ 64 -> bytes_at asegs m a (u64s ws).
  Proof.
    induction ws as [|w ws IH]; intros m a HR Ha Hn.
    - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    - change (u64s (w :: ws)) with (le8 w ++ u64s ws). apply (proj2 (bytes_at_app _ _ _ _ _)). split.
      + apply rdnA_bytes_at; [| lia | rewrite length_le8; cbn [length] in Hn; lia].
        rewrite length_le8. replace a with (a + 8 * Z.of_nat 0) by lia. unfold le8. exact (HR 0%nat w eq_refl).
      + rewrite length_le8. apply IH; [| lia | cbn [length] in Hn; lia].
        intros i w' Hi. replace (a + Z.of_nat 8 + 8 * Z.of_nat i) with (a + 8 * Z.of_nat (S i)) by lia. apply HR. exact Hi.
  Qed.

  Theorem auxv_ok_main : forall (HCEIL : HeapCeil), @hceil HCEIL = sp0z - 8388608 -> @aauxv_ok HCEIL VM sp0z.
  Proof.
    intros HCEIL HHC. pose proof auxv_lay_main as (L1 & L2 & L3 & L4). pose proof (@aceil_le_hceil HCEIL) as ACH.
    destruct (auxv_val_main 0 ltac:(lia)) as [w0 W0]. destruct (auxv_val_main 1 ltac:(lia)) as [w1 W1].
    destruct (auxv_val_main 2 ltac:(lia)) as [w2 W2]. destruct (auxv_val_main 3 ltac:(lia)) as [w3 W3].
    destruct (auxv_val_main 4 ltac:(lia)) as [w4 W4]. destruct (auxv_val_main 5 ltac:(lia)) as [w5 W5].
    destruct (auxv_val_main 6 ltac:(lia)) as [w6 W6]. destruct (auxv_val_main 7 ltac:(lia)) as [w7 W7].
    destruct (auxv_val_main 8 ltac:(lia)) as [w8 W8]. destruct (auxv_val_main 9 ltac:(lia)) as [w9 W9].
    exists av, (bv_unsigned w0), (bv_unsigned w1), (bv_unsigned w2), (bv_unsigned w3), (bv_unsigned w4),
           (bv_unsigned w5), (bv_unsigned w6), (bv_unsigned w7), (bv_unsigned w8), (bv_unsigned w9).
    pose proof (u64_range w0). pose proof (u64_range w1). pose proof (u64_range w2). pose proof (u64_range w3). pose proof (u64_range w4).
    pose proof (u64_range w5). pose proof (u64_range w6). pose proof (u64_range w7). pose proof (u64_range w8). pose proof (u64_range w9).
    split; [| split; [| unfold AAUXV_CELL; lia]].
    - (* [comment removed for export] *)
      unfold AAUXV_CELL. apply rw_cells_img; [cbn; tauto | lia | cbn; lia |].
      cbn [cells_bytes cbytes app]. rewrite app_nil_r.
      apply rdnA_bytes_at; [| lia | rewrite length_le8; lia]. rewrite length_le8. unfold le8, TacX.wz.
      exact auxv_cell_main.
    - (* [comment removed for export] *)
      replace (av + 16 * 0 + 8) with (av + (16 * 0 + 8)) in W0 by lia. replace (av + 16 * 1 + 8) with (av + (16 * 1 + 8)) in W1 by lia.
      replace (av + 16 * 2 + 8) with (av + (16 * 2 + 8)) in W2 by lia. replace (av + 16 * 3 + 8) with (av + (16 * 3 + 8)) in W3 by lia.
      replace (av + 16 * 4 + 8) with (av + (16 * 4 + 8)) in W4 by lia. replace (av + 16 * 5 + 8) with (av + (16 * 5 + 8)) in W5 by lia.
      replace (av + 16 * 6 + 8) with (av + (16 * 6 + 8)) in W6 by lia. replace (av + 16 * 7 + 8) with (av + (16 * 7 + 8)) in W7 by lia.
      replace (av + 16 * 8 + 8) with (av + (16 * 8 + 8)) in W8 by lia. replace (av + 16 * 9 + 8) with (av + (16 * 9 + 8)) in W9 by lia.
      pose proof (fun i (Hi : 0 <= i < 10) => auxv_key_main i Hi) as KEY.
      apply bytes_at_words; [| lia | rewrite aauxv_list_length; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia].
      intros i w Hi. unfold aauxv_list in Hi.
      do 20 (destruct i as [|i];
        [ cbn [nth_error map] in Hi; injection Hi as <-;
          first [ exact (KEY 0 ltac:(lia)) | exact (KEY 1 ltac:(lia)) | exact (KEY 2 ltac:(lia)) | exact (KEY 3 ltac:(lia)) | exact (KEY 4 ltac:(lia))
                | exact (KEY 5 ltac:(lia)) | exact (KEY 6 ltac:(lia)) | exact (KEY 7 ltac:(lia)) | exact (KEY 8 ltac:(lia)) | exact (KEY 9 ltac:(lia))
                | (unfold TacX.wz; rewrite Z_to_bv_bv_unsigned;
                   first [exact W0 | exact W1 | exact W2 | exact W3 | exact W4 | exact W5 | exact W6 | exact W7 | exact W8 | exact W9]) ]
        |]).
      destruct i; cbn [nth_error map] in Hi; discriminate Hi.
  Qed.
End AT_MAIN.
