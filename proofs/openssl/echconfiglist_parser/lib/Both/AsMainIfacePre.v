(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsCellOk ECH_Xpres AsPrintfFirst AsDrvDefs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsHSTab AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
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
  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  #[local] Notation MR := (Mr ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model FULL).
  #[local] Notation HID := (hid ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model).
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vm_sub : forall a b, VM a = Some b -> FULL a = Some b.
  Proof.
    intros a b H. unfold pm_vmem, restrict_mem, restrict_mem_by in H. destruct (hiddenb _ _ a); [discriminate | exact H].
  Qed.
  Lemma vm_none_of : forall a, FULL a = None -> VM a = None.
  Proof. intros a H. unfold pm_vmem, restrict_mem, restrict_mem_by. destruct (hiddenb _ _ a); [reflexivity | exact H]. Qed.

  Lemma img_none_main : forall lo hi, img_check lo hi = true -> forall i, lo <= i < hi -> VM (Z_to_bv 64 i) = None.
  Proof. intros lo hi H i Hi. apply vm_none_of. exact (pmc_img _ _ _ _ _ _ MC lo hi H i Hi). Qed.

  Lemma pre_relro : arelro_none VM.
  Proof. exact (img_none_main 0x571000 0x5ea000 ltac:(vm_cast_no_check (@eq_refl bool true))). Qed.
  Lemma pre_ro : aro_none VM.
  Proof. exact (img_none_main 0x10000 0x195000 ltac:(vm_cast_no_check (@eq_refl bool true))). Qed.
  Lemma pre_glb : aglb_none VM.
  Proof.
    split; [exact (img_none_main 0x5edd90 0x5ede88 ltac:(vm_cast_no_check (@eq_refl bool true))) |].
    intros i [Hi _]. exact (img_none_main 0x5edf70 0x6a7220 ltac:(vm_cast_no_check (@eq_refl bool true)) i Hi).   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma pre_inv : mem_inv asegs VM.
  Proof.
    intros a b H. unfold ro_addr. rewrite asegs_ASEGS.
    destruct (find_segment ASEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|reflexivity].
    apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asan_segs_eq in Hin.
    destruct (seg_writable seg) eqn:SW; [reflexivity|]. exfalso.
    assert (HR : 0x10000 <= bv_unsigned a < 0x571000).
    { destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hb, Ht, SW; try discriminate SW; lia. }
    pose proof (img_none_main 0x10000 0x571000 ltac:(vm_cast_no_check (@eq_refl bool true)) (bv_unsigned a) HR) as N.
    replace (Z_to_bv 64 (bv_unsigned a)) with a in N by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range). congruence.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bytes_eqb (xs ys : list byte) : bool := list_eqb (fun x y => Z.eqb (bv_unsigned x) (bv_unsigned y)) xs ys.
  Lemma bytes_eqb_eq : forall xs ys, bytes_eqb xs ys = true -> xs = ys.
  Proof.
    intros xs ys H. apply (list_eqb_eq _) in H; [exact H|]. intros x y Hxy. apply Z.eqb_eq in Hxy. apply bv_eq. exact Hxy.
  Qed.
  (* [comment removed for export] *)
  Definition rom_cell_check (c : Z * nat * Z) : bool :=
    let '(a, w, v) := c in
    img_check a (a + Z.of_nat w)
    && match rdn ASEGS (fun _ => None) (Z_to_bv 64 a) w with
       | Some bs => bytes_eqb bs (word_to_le_bytes w (Z_to_bv 64 v)) | None => false end.
  (* [comment removed for export] *)
  Definition ovl_cell_check (c : Z * nat * Z) : bool :=
    let '(a, w, v) := c in
    Z.leb 0x571000 a && Z.leb (a + Z.of_nat w) 0xc04000 && bytes_check (CAbs, a) (map bv_unsigned (word_to_le_bytes w (Z_to_bv 64 v))).
  Definition cell_check (c : Z * nat * Z) : bool := rom_cell_check c || ovl_cell_check c.

  Lemma rom_cell_main : forall c, rom_cell_check c = true -> cell_ok VM c.
  Proof.
    intros [[a w] v] H. unfold rom_cell_check in H. apply andb_prop in H as [HI HR].
    pose proof HI as HI'. unfold img_check in HI'. apply andb_prop in HI' as [HI' _]. apply andb_prop in HI' as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (rdn ASEGS (fun _ => None) (Z_to_bv 64 a) w) as [bs|] eqn:RD; [|discriminate]. apply bytes_eqb_eq in HR. subst bs.
    unfold cell_ok. rewrite <- RD. apply rdn_ext; [rewrite u_of_Z by lia; lia|].
    intros x Hx. rewrite u_of_Z in Hx by lia. replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range). apply (img_none_main _ _ HI). lia.
  Qed.
  Lemma ovl_cell_main : forall c, ovl_cell_check c = true -> cell_ok VM c.
  Proof.
    intros [[a w] v] H. unfold ovl_cell_check in H. apply andb_prop in H as [H HB]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    assert (HL : length (word_to_le_bytes w (Z_to_bv 64 v)) = w) by apply CatExec.length_N_to_le_bytes.
    pose proof (bytes_main w_all (CAbs, a) _ HB (world_ok_all _ _)) as B. revert B. pmc_simpl. rewrite !length_map, HL, Z.add_0_l. intros B.
    specialize (B ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)). rewrite map_b8_unsigned in B.
    unfold cell_ok. pose proof (bytes_at_rdn asegs VM a _ 0 w B ltac:(rewrite HL; lia)) as RD.
    rewrite Nat2Z.inj_0, Z.add_0_r, skipn_O in RD. rewrite firstn_all2 in RD by (rewrite HL; lia).
    exact RD.
  Qed.
  Lemma cells_main : forall cs, forallb cell_check cs = true -> cells_ok VM cs.
  Proof.
    intros cs H. unfold cells_ok. apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) H c Hc) as H1.
    unfold cell_check in H1. apply orb_prop in H1 as [H1|H1]; [apply rom_cell_main | apply ovl_cell_main]; exact H1.
  Qed.

  Lemma pre_cells : cells_ok VM adrv_cells.
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma pre_out : cells_ok VM astdout0.
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kword_check_w (w : world) (a : cx) (wd : nat) (ve : expr) : bool :=
    all_holes_w w (fun g cls ch => let (b, k) := csym_base g cls (fst a) in existsb (kentry_eqb (KWord (SA b (k + snd a)) wd ve)) (kn ch)).
  Lemma kword_main : forall w a wd ve, kword_check_w w a wd ve = true -> world_ok w (pm_short sp0z) g -> (0 < wd)%nat ->
    0 <= CXV a -> CXV a + Z.of_nat wd <= 2 ^ 64 -> vrange (CXV a) (CXV a + Z.of_nat wd) ->
    rdn ASEGS VM (Z_to_bv 64 (CXV a)) wd = Some (word_to_le_bytes wd (edenot E ve)).
  Proof.
    intros w [s off] wd ve H Hw Hwd0 H0 H1 VR. apply (all_holes_w_here w) in H; [|exact (hole_sel_here w Hw)].
    cbn [fst snd] in H.
    destruct (csym_den s) as (D1 & D2 & D3).
    destruct (csym_base g cls s) as [b k] eqn:CB. cbn [fst snd] in D1, D2, D3.
    apply existsb_exists in H as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. cbn [kentry_ok] in KO. destruct KO as (Hwd & FL & RD).
    assert (HE : estart E (SA b (k + off)) = CXV (s, off)).
    { unfold estart. cbn [a_base a_off]. fold (uE E b). revert D1. pmc_simpl. intros D1. lia. }
    assert (Ha : adenot E (SA b (k + off)) = Z_to_bv 64 (CXV (s, off))).
    { apply bv_eq. rewrite (flat_u E _ _ FL), HE, u_of_Z; [reflexivity|]. pose proof (u64_range (adenot E (SA b (k + off)))) as RR. rewrite (flat_u E _ _ FL), HE in RR. exact RR. }
    rewrite Ha in RD.
    assert (RF : rdn ASEGS FULL (Z_to_bv 64 (CXV (s, off))) wd = Some (word_to_le_bytes wd (edenot E ve))).
    { apply (rdn_Mr_full _ _ _ RD).
      intros i Hi. rewrite u_of_Z by lia. eapply visibleZ_hid.
      destruct (VR (CXV (s, off) + i) ltac:(lia)) as [_ V]. exact V. }
    rewrite <- RF. apply rdn_ext; [rewrite u_of_Z by lia; lia|]. intros x Hx. rewrite u_of_Z in Hx by lia.
    destruct (VR (bv_unsigned x) ltac:(lia)) as [V _]. unfold wa in V. replace (Z_to_bv 64 (bv_unsigned x)) with x in V by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range). exact V.
  Qed.

  Lemma pre_tid : atid_cell VM (ps_tid X).
  Proof.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & VTID & _).
    split; [|unfold Xof; cbn [ps_tid]; lia].
    pose proof (kword_main w_all (CAbs, 0xbe1be8) 4 (EVar K_TID) ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)) as W.
    revert W. pmc_simpl. rewrite Z.add_0_l. intros W. change AsanUbsan.M.loaded_segments with ASEGS.
    rewrite (W ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)). do 2 f_equal. apply bv_eq.
    unfold Xof. cbn [ps_tid]. change (bv_unsigned (edenot E (EVar K_TID))) with (vE E K_TID). rewrite u_of_Z; [reflexivity | lia].
  Qed.

  Lemma pre_can : exists can, acanary VM can.
  Proof.
    exists (bv_unsigned (edenot E (EVar 61))). split; [|apply u64_range].
    pose proof (kword_main w_all (CAbs, 0xc01cd0) 8 (EVar 61) ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)) as W.
    revert W. pmc_simpl. rewrite Z.add_0_l. intros W. change AsanUbsan.M.loaded_segments with ASEGS.
    rewrite (W ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)). do 2 f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma Z_to_le_bytes_le : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
  Proof.
    clear. induction bs as [|b bs IH]; cbn [length Z_to_le_bytes bytes_le_to_Z]; [reflexivity|].
    pose proof (bv_unsigned_in_range _ b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
    pose proof (PropExec.bytes_le_to_Z_nonneg bs) as Hr.
    f_equal.
    - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
      rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
      rewrite (Z.land_ones (bv_unsigned b) 8) by lia. rewrite (Z.mod_small (bv_unsigned b)) by (change (2^8) with 256; lia).
      replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0; [apply Z.lor_0_r|].
      symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases i 8) as [H8|H8].
      + rewrite Z.shiftl_spec_low by lia. reflexivity.
      + rewrite Z.ones_spec_high by lia. apply andb_false_r.
    - rewrite Z.shiftr_lor. rewrite Z.shiftr_shiftl_l by lia. change (8 - 8) with 0. rewrite Z.shiftl_0_r.
      rewrite (Z.shiftr_div_pow2 (bv_unsigned b)) by lia. rewrite Z.div_small by (change (2^8) with 256; lia). rewrite Z.lor_0_l. exact IH.
  Qed.
  Lemma rw_byte_main : forall z, 0x571000 <= z < 0xc04000 -> exists b, mrd asegs VM (wa z) = Some b.
  Proof.
    intros z Hz. unfold mrd. destruct (VM (wa z)) as [b|]; [exists b; reflexivity|].
    rewrite seg_rom_lib, asegs_ASEGS. exact (img_rw_rom z Hz).
  Qed.
  Lemma rw_bytes_main : forall n a, 0x571000 <= a -> a + Z.of_nat n <= 0xc04000 -> exists bs, length bs = n /\ bytes_at asegs VM a bs.
  Proof.
    induction n as [|n IH]; intros a H0 H1.
    - exists []. split; [reflexivity|]. apply bytes_at_of_nth; [lia | cbn [length]; lia |]. intros i Hi. cbn [length] in Hi. lia.
    - destruct (rw_byte_main a ltac:(lia)) as [b Hb]. destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & HB).
      exists (b :: bs). split; [cbn [length]; lia|]. apply bytes_at_of_nth; [lia | cbn [length]; lia |].
      intros i Hi. destruct i as [|i]; cbn [nth_error].
      + rewrite Z.add_0_r. exact Hb.
      + destruct HB as (_ & _ & HB). replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. apply HB. cbn [length] in Hi. lia.
  Qed.

  Lemma pre_errno : exists e, rw_cells asegs VM AERRNO [C4 e].
  Proof.
    unfold AERRNO, ATP.
    destruct (rw_bytes_main 4 (12459152 - 164) ltac:(lia) ltac:(lia)) as (bs & Hl & HB).
    exists (Z_to_bv 64 (bytes_le_to_Z bs)).
    apply rw_cells_img; [cbn; tauto | lia | csz; lia |].
    replace (cells_bytes [C4 (Z_to_bv 64 (bytes_le_to_Z bs))]) with bs; [exact HB|].
    cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4.
    pose proof (PropExec.bytes_le_to_Z_bound bs) as B1. pose proof (PropExec.bytes_le_to_Z_nonneg bs) as B0. rewrite Hl in B1.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in B1; lia).
    transitivity (Z_to_le_bytes (length bs) (bytes_le_to_Z bs)); [symmetry; apply Z_to_le_bytes_le | rewrite Hl; reflexivity].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pre_reg : cells_ok VM aatexit_pre_cells.
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.

  (* [comment removed for export] *)
  Lemma pre_lib : forall ivs, (forall iv, In iv ivs -> img_check (fst iv) (snd iv) = true) ->
    forall i, rin_ivs ivs i -> VM (Z_to_bv 64 i) = None.
  Proof.
    induction ivs as [|iv ivs IH]; intros HC' i Hi; [destruct Hi|].
    destruct Hi as [Hi|Hi]; [exact (img_none_main _ _ (HC' iv (or_introl eq_refl)) i Hi) | exact (IH (fun iv' Hin => HC' iv' (or_intror Hin)) i Hi)].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kwr1 (bc : bctx) (qa : lin) (n : Z) (K : kentry) : bool :=
    match K with
    | KWr za (ELit zn) =>
        match lin_ofaB bc za with
        | Some l0 => le_linB bc l0 qa && le_linB bc qa l0 && Z.leb n zn && Z.leb 0 zn && Z.ltb zn (2 ^ 62)
        | None => false end
    | _ => false
    end.
  (* [comment removed for export] *)
  Definition kzero1 (bc : bctx) (qa qn : lin) (K : kentry) : bool :=
    match K with
    | KZero za zn =>
        match lin_ofaB bc za, lin_ofxB bc zn with
        | Some l0, Some ln => le_linB bc l0 qa && le_linB bc qa l0 && le_linB bc qn ln
        | _, _ => false end
    | _ => false
    end.
  (* [comment removed for export] *)
  Definition LSTK : lin := (-8388608, [(32768, EVar 0); (4096, EVar 6); (16, EVar 10)]).
  Definition LSHSTK : lin := (2146402304, [(4096, EVar 0); (512, EVar 6)]).
  Definition LSHLEN : lin := (17592187092992, [(-4096, EVar 0); (-512, EVar 6)]).
  Definition stk_check : bool := all_holes (fun g cls ch => existsb (kwr1 (mkbc (kn ch)) LSTK 8388608) (kn ch)).
  Definition shz_check : bool := all_holes (fun g cls ch => existsb (kzero1 (mkbc (kn ch)) LSHSTK LSHLEN) (kn ch)).
  Lemma stk_check_ok : stk_check = true.  Proof. vm_compute. reflexivity. Qed.
  Lemma shz_check_ok : shz_check = true.  Proof. vm_compute. reflexivity. Qed.

  Lemma lden_LSTK : lden E LSTK = sp0z - 8388608.
  Proof.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & SP & _).
    unfold LSTK, lden. cbn [fst snd tden]. rewrite !uE_var. lia.
  Qed.
  Lemma lden_LSH : lden E LSHSTK = SHOFF + (page_down sp0z - 8388608) / 8 /\ lden E LSHSTK + lden E LSHLEN = SHOFF + 2 ^ 44.
  Proof.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PGD & _).
    unfold LSHSTK, LSHLEN, lden, SHOFF. cbn [fst snd tden]. rewrite !uE_var. rewrite <- PGD. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_full : forall z, sp0z - 8388608 <= z < sp0z -> exists b, FULL (wa z) = Some b.
  Proof.
    intros z Hz. pose proof stk_check_ok as H0. unfold stk_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply existsb_exists in H as [K [HK HW]]. pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO.
    destruct K as [| | | | | | a [zn| | | | | | |] | | |]; try discriminate HW. cbn [kwr1] in HW.
    destruct (lin_ofaB (mkbc (kn ch)) a) as [l0|] eqn:L0; [|discriminate].
    apply andb_prop in HW as [HW H5]. apply andb_prop in HW as [HW H4]. apply andb_prop in HW as [HW H3]. apply andb_prop in HW as [H1 H2].
    rewrite lin_ofaB_eqf in L0. rewrite le_linB_eqf in H1, H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.ltb_lt in H5.
    pose proof (lin_ofa_sound _ _ _ _ KNF _ _ L0) as S0.
    apply (le_lin_sound _ _ _ _ KNF) in H1. apply (le_lin_sound _ _ _ _ KNF) in H2. rewrite lden_LSTK in H1, H2.
    cbn [kentry_ok] in KO. destruct KO as [FL ST]. unfold elenZ in ST. fold (uE E (ELit zn)) in ST.
    rewrite (uE_lit' zn ltac:(lia)) in ST.
    specialize (ST (z - estart E a) 1%nat ltac:(lia) ltac:(lia)). replace (estart E a + (z - estart E a)) with z in ST by lia.
    cbn [store_ok] in ST. fold (wa z) in ST.
    destruct (wview ASEGS MR (wa z)) as [b|] eqn:WV; [|discriminate].
    unfold wview in WV. destruct (MR (wa z)) as [b'|] eqn:HM.
    - exists b'. exact (Mr_some' _ _ HM).
    - exfalso. pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
      rewrite wa_unsigned in WV by lia.
      destruct (find_segment ASEGS z 1) as [seg|] eqn:Hf; [|discriminate].
      apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asan_segs_eq in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hb, Ht; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_stk : forall lo, sp0z - 8388608 <= lo -> lo <= sp0z -> stk asegs VM lo sp0z.
  Proof.
    intros lo H1 H2. pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    pose proof pd_facts as PD.
    apply stk_of_some; [lia | lia |]. intros a Ha.
    destruct (stack_full a ltac:(lia)) as [b Hb]. exists b. rewrite <- Hb. apply vm_stack. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_shadow_zero : forall z, SHOFF + (page_down sp0z - 8388608) / 8 <= z < SHOFF + 2 ^ 44 -> VM (wa z) = Some (b8 0).
  Proof.
    intros z Hz. pose proof lden_LSH as [D1 D2]. pose proof pd_facts as PD.
    pose proof shz_check_ok as H0. unfold shz_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply existsb_exists in H as [K [HK HW]]. pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO.
    destruct K as [| a zn | | | | | | | |]; try discriminate HW. cbn [kzero1] in HW.
    destruct (lin_ofaB (mkbc (kn ch)) a) as [l0|] eqn:L0; [|discriminate]. destruct (lin_ofxB (mkbc (kn ch)) zn) as [ln|] eqn:LN; [|discriminate].
    apply andb_prop in HW as [HW H3]. apply andb_prop in HW as [H1 H2].
    rewrite lin_ofaB_eqf in L0. rewrite lin_ofxB_eqf in LN. rewrite le_linB_eqf in H1, H2, H3.
    pose proof (lin_ofa_sound _ _ _ _ KNF _ _ L0) as S0. pose proof (lin_ofx_sound _ _ _ _ KNF _ _ LN) as SN.
    apply (le_lin_sound _ _ _ _ KNF) in H1. apply (le_lin_sound _ _ _ _ KNF) in H2. apply (le_lin_sound _ _ _ _ KNF) in H3.
    cbn [kentry_ok] in KO. destruct KO as [FL Z0]. unfold elenZ in Z0. unfold uE in SN. rewrite SN in Z0.
    assert (HF : FULL (wa z) = Some (b8 0)).
    { apply Mr_some'. unfold wa. replace z with (estart E a + (z - estart E a)) by lia. apply Z0. lia. }
    rewrite <- HF. replace z with (SHOFF + (8 * (z - SHOFF)) / 8) by (unfold SHOFF in *; lia).
    apply (vm_sw (page_down sp0z - 8388608) (140737496743936 - page_down sp0z)); [| lia | unfold SHOFF in *; lia | lia | ].
    - unfold VISZ, VISZ0. apply in_or_app. left. do 18 right. left. reflexivity.
    - replace (page_down sp0z - 8388608 + (140737496743936 - page_down sp0z)) with (17592186044416 * 8) by lia. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_sh0 : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    forall lo, page_down sp0z - 8388608 <= lo <= 2 ^ 47 -> exists shi, stack0 VM lo shi /\ 0x800000000000 <= shi.
  Proof.
    intros HCEIL Hh' lo Hlo. pose proof pd_facts as (PD1 & PD2 & PD3). exists (2 ^ 47). split; [|lia].
    assert (AC : aceil = page_down sp0z - 8388608).
    { unfold aceil. rewrite Hh'. unfold AsMainSyms.page_down in *. lia. }
    exists aceil. rewrite AC. unfold AAPP_HI. split; [lia|]. split; [lia|].
    split; [lia|].
    unfold addressable. split; [lia|]. unfold SHAD. split; [lia|]. split; [lia|].
    unfold sh. rewrite ASHADOW_BASE_val. fold SHOFF.
    rewrite (shadow_of_mult8 (2 ^ 47 - (page_down sp0z - 8388608)) ltac:(lia) ltac:(lia)).
    apply u8arr_constZ; [unfold SHOFF; lia | lia | unfold SHOFF; lia |].
    intros z Hz. apply stack_shadow_zero. unfold SHOFF in *. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let PMo := PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC.
  Lemma pre_regs : getr R 1 = Z_to_bv 64 0x55de4c /\ getr R 2 = Z_to_bv 64 (sp0z - 48) /\ getr R 4 = Z_to_bv 64 ATP
                   /\ getr R 10 = Z_to_bv 64 argc /\ getr R 11 = Z_to_bv 64 (sp0z + 8).
  Proof.
    pose proof (pm_regs _ _ _ _ _ PMo) as RG. cbv zeta in RG. cbn [cfg_ms cfg_of mkst ms_regs] in RG.
    destruct RG as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & _). unfold ATP.
    repeat split; try assumption; rewrite R2; f_equal; lia.
  Qed.
  Lemma pre_fds : m_fds model = [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
  Proof. exact (pm_fds _ _ _ _ _ PMo). Qed.
  Lemma pre_fs : m_fs model = in_fs inp.
  Proof. exact (pm_fs _ _ _ _ _ PMo). Qed.
End AT_MAIN.
