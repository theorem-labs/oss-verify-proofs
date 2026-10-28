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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsHSTab AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface AsMainIfacePre. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsPlanImagesHex AsPlanImagesHexZ.
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
  #[local] Notation lz_facts := (AsMainLazy.facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_lazy := (AsMainLazy.zz_ok_lazy sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_S := (AsMainLazy.zz_ok_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_maps := (AsMainLazy.zz_ok_maps sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_noacc := (AsMainLazy.zz_ok_noacc sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_ok_zr := (AsMainLazy.zz_ok_zr sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation PM_maps_eq := (AsMainLazy.PM_maps_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation PM_lazy_eq := (AsMainLazy.PM_lazy_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation PM_noacc_eq := (AsMainLazy.PM_noacc_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation in_rangesb_zz := (AsMainLazy.in_rangesb_zz sp0 brk0) (only parsing).
  #[local] Notation zin_spec := (AsMainLazy.zin_spec sp0 brk0) (only parsing).
  (* [comment removed for export] *)
  #[local] Notation kword_main := (AsMainIfacePre.kword_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  (* [comment removed for export] *)
  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rw_cells_out : forall m A cs, cells_wf cs -> 0 <= A -> (A + Z.of_nat (cells_size cs) <= 65536 \/ 0xc04000 <= A) ->
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
    (hi <= 65536 \/ 0xc04000 <= lo) -> hi <= 2 ^ 64 -> rw_cells asegs VM (CXV a) [C8 (wz (CXV v))].
  Proof.
    intros a v lo hi Hc VR H0 H1 H2 H3 H4. apply rw_cells_out; [cbn; tauto | lia | csz; lia | csz; lia |].
    exact (word_main w_all a v Hc (world_ok_all _ _) ltac:(lia) ltac:(lia) (vr_sub _ _ _ _ VR H0 H1)).
  Qed.
  Lemma obj_bytes_out : forall a cs lo hi, bytes_check a (cellsZ cs) = true -> cells_wfb cs = true -> vrange lo hi ->
    lo <= CXV a -> CXV a + Z.of_nat (cells_size cs) <= hi -> 0 <= lo -> (hi <= 65536 \/ 0xc04000 <= lo) -> hi <= 2 ^ 64 ->
    rw_cells asegs VM (CXV a) cs.
  Proof.
    intros a cs lo hi Hc WF VR H0 H1 H2 H3 H4. apply cells_wfb_sound in WF. apply rw_cells_out; [exact WF | lia | lia | lia |].
    rewrite <- map_b8_cellsZ. apply (bytes_main w_all a (cellsZ cs) Hc (world_ok_all _ _)); rewrite ?(length_cellsZ cs WF); [lia | lia |].
    eapply vr_sub; [exact VR | lia | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma zero_cells : forall lo hi A cs, (forall z, lo <= z < hi -> VM (wa z) = Some (b8 0)) ->
    cells_wf cs -> cells_bytes cs = repeat (b8 0) (cells_size cs) -> 0 <= lo -> (hi <= 65536 \/ 0xc04000 <= lo) -> hi <= 2 ^ 64 ->
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
  (* [comment removed for export] *)
  Lemma img_stk : forall lo hi, 0x571000 <= lo -> lo <= hi -> hi <= 0xc04000 -> stk asegs VM lo hi.
  Proof. intros lo hi H0 H1 H2. apply stk_img_rw; lia. Qed.
  Lemma img_wr : forall a n, 0x571000 <= a -> a + n <= 0xc04000 -> wr_at asegs VM a n.
  Proof. intros a n H0 H1. apply wr_at_img_rw; lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma al_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> aceil = page_down sp0z - 8388608.
  Proof. intros HCEIL Hh'. pose proof pd_facts as (PD1 & PD2 & PD3). unfold aceil. rewrite Hh'. unfold AsMainSyms.page_down in *. lia. Qed.
  Lemma al_top : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> alloc_top (m_vmmaps model) = hceil /\ aceil <= hceil < aceil + 4096.
  Proof.
    intros HCEIL Hh'. pose proof (al_ceil HCEIL Hh') as AC. pose proof pd_facts as (PD1 & PD2 & PD3).
    pose proof (pm_topz _ _ _ _ _ (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)) as T.
    cbn [cfg_model cfg_of] in T. unfold TOP, pm_top in T. rewrite AC, Hh'. lia.
  Qed.
  Definition geo (p : Z * Z) : Prop :=
    fst p mod 4096 = 0 /\ 4096 <= fst p /\ fst p + snd p <= page_down sp0z - 8388608
    /\ (fst p + snd p <= 65536 \/ 12599296 <= fst p) /\ (fst p + snd p <= 2147446784 \/ 17594333495296 <= fst p).
  Lemma al_T   : geo (ps_b09 X, 4096).          Proof. exact (kp_facts _ _ kp_b09). Qed.
  Lemma al_CTX : geo (ps_b10 X, 0x10000).       Proof. exact (kp_facts _ _ kp_b10). Qed.
  Lemma al_R6  : geo (ps_b06 X, 0x2000011000).  Proof. exact (kp_facts _ _ kp_b06). Qed.
  Lemma al_PA  : geo (ps_b08 X, 0x800000).      Proof. exact (kp_facts _ _ kp_b08). Qed.
  Lemma al_FSB : geo (ps_b16 X, 0xb09000).      Proof. exact (kp_facts _ _ kp_b16). Qed.
  Lemma al_D   : geo (ps_b12 X, 4096).          Proof. exact (kp_facts _ _ kp_b12). Qed.
  Lemma al_B11 : geo (ps_b11 X, 4096).          Proof. exact (kp_facts _ _ kp_b11). Qed.
  (* [comment removed for export] *)
  Lemma al_SB : pm_space_beg X mod 65536 = 0 /\ ps_b06 X < pm_space_beg X <= ps_b06 X + 65536
                /\ pm_region_info X = pm_space_beg X + 2 ^ 37
                /\ pm_region_info X + 4096 <= ps_b06 X + 0x2000011000 /\ 17594333495296 <= ps_b06 X
                /\ ps_b06 X + 0x2000011000 <= page_down sp0z - 8388608.
  Proof.
    pose proof al_R6 as (G1 & G2 & G3 & G4 & G5). cbn [fst snd] in G1, G2, G3, G4, G5. pose proof (pso_spacebeg _ _ _ _ SOK) as [S1 S2].
    unfold pm_region_info. lia.
  Qed.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Lemma al_stack : pm_stack_top sp0z mod 4096 = 0 /\ sp0z - 160 <= pm_stack_top sp0z < sp0z - 160 + 4096
                   /\ 0x7fff80000000 <= pm_stack_top sp0z <= 0x800000000000 /\ pm_stack_bottom sp0z = pm_stack_top sp0z - 8388608.
  Proof.
    pose proof pd_facts as (PD1 & PD2 & PD3). pose proof lz_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VSP).
    unfold pm_stack_bottom, pm_stack_top, AsMainSyms.page_up. unfold AsMainSyms.page_down in *.
    split; [apply Z_mod_mult|].
    pose proof (Z.div_mod (sp0z - 160 + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sp0z - 160 + 4095) 4096 ltac:(lia)).
    assert (sp0z / 4096 <= (sp0z - 160 + 4095) / 4096) by (apply Z.div_le_mono; lia). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition al_lits : list (Z * list cell) :=
    [ (0x6a7298 + 40, [C4 (wz 0xffffffff); C4 (wz 0)]);                 (* [comment removed for export] *)
      (0x6a7298 + 56, [C8 (wz 0); C8 (wz 4096)]);                        (* [comment removed for export] *)
      (0x6a7298 + 88, [C8 (wz 0x800000)]);                                 (* [comment removed for export] *)
      (0x6a7298 + 112, [C8 (wz 0); C8 (wz 0); C8 (wz 0)]);                (* [comment removed for export] *)
      (0x6a7298 + 680, [C8 (wz 0)]);                                       (* [comment removed for export] *)
      (0x6a7298 + 792, [C8 (wz 0x10000000); C8 (wz 0xE666661); C8 (wz 0x100000)]);   (* [comment removed for export] *)
      (0x6a7298 + 880, [C8 (wz 0)]);                                       (* [comment removed for export] *)
      (0x6a7298 + 888, [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]);    (* [comment removed for export] *)
      (0x6a7298 + 984, [C8 (wz 0)]);                                       (* [comment removed for export] *)
      (0x6a7298 + 3616, [C8 (wz (2 ^ 40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]]); (* [comment removed for export] *)
      (0x6a80f8 + 44, [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)]);           (* [comment removed for export] *)
      (0x6a80f8 + 78, [C1 (b8 1)]); (0x6a80f8 + 85, [C1 (b8 1)]); (0x6a80f8 + 88, [C1 (b8 1)]);   (* [comment removed for export] *)
      (0x73c428 + 34, [C1 (b8 1)]); (0x73c428 + 120, [C8 (wz 0xffffffffffffffff)]); (0x73c428 + 144, [C8 (wz 0)]); (0x73c428 + 260, [C1 (b8 0)]); (* [comment removed for export] *)
      (0x73c428 + 219, [C1 (b8 1)]); (0x73c428 + 244, [C1 (b8 1)]);      (* [comment removed for export] *)
      (0x6aa8f8, [C8 (wz 0x7fff8000)]);                                    (* [comment removed for export] *)
      (0x6ab5e0, [C8 (wz (2 ^ 47 - 1)); C8 (wz 0); C8 (wz 0)]);            (* [comment removed for export] *)
      (0x6aa15c, [C1 (b8 1)]);                                              (* [comment removed for export] *)
      (0x6ab5d8, [C1 (b8 1)]);                                              (* [comment removed for export] *)
      (0x6ab5fc, [C4 (wz 30)]);                                             (* [comment removed for export] *)
      (0x6aa160, [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)]);         (* [comment removed for export] *)
      (0x72cb60, [C1 (b8 0); C1 (b8 1); C1 (b8 0)]);                       (* [comment removed for export] *)
      (0x73a388, [C1 (b8 0); C1 (b8 0); C2 (wz 0)]);                       (* [comment removed for export] *)
      (0x73c3c0, [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]); (* [comment removed for export] *)
      (0x73c41c, [C4 (wz 0)]);                                              (* [comment removed for export] *)
      (0x5eaa70, [C8 (wz 0x569e10)]);                                       (* [comment removed for export] *)
      (0x5e77f8, map (fun v => C8 (wz v))
         [0x73a3a0; 0x5eaaa8; 0x73c428; 0x6a80f8; 0x6aa8f8; 0x6ab5e8; 0x6ab5f0; 0x6ab5e0; 0x5eaa70; 0x5eaa68; 0x5eaaa0; 0x5eaab8; 1; 0x73c41c; 0x73a398]);
                                                                             (* [comment removed for export] *)
      (0x73a3a0, [C8 (wz 4096)]);                                           (* [comment removed for export] *)
      (0x5eaaa8, [C8 (wz 0x2ebe7)]);                                        (* [comment removed for export] *)
      (0x5eaab8, [C8 (wz 0x478d1)]);                                        (* [comment removed for export] *)
      (0xbe1c38, [C8 (wz 0xc03038)]);                                       (* [comment removed for export] *)
      (0xbe1cb0, [C4 (wz 0)]);                                              (* [comment removed for export] *)
      (0x5e8490, [C8 (wz 0x20)]);                                           (* [comment removed for export] *)
      (0xc01f50, [C8 (wz 4096)]);                                           (* [comment removed for export] *)
      (0x5e9798, [C8 (wz 0xc01cd0)]) ].                                    (* [comment removed for export] *)
  Lemma al_lits_check : forallb (fun ac => img_cells_check (fst ac) (snd ac)) al_lits = true.
  Proof. vm_cast_no_check (@eq_refl bool true). Qed.   (* [comment removed for export] *)
  Lemma al_lits_main : Forall (fun ac => rw_cells asegs VM (fst ac) (snd ac)) al_lits.
  Proof. apply Forall_forall. intros ac Hin. apply img_cells_main. exact (proj1 (forallb_forall _ _) al_lits_check ac Hin). Qed.
  (* [comment removed for export] *)
  Lemma al_lit : forall A cs, In (A, cs) al_lits -> rw_cells asegs VM A cs.
  Proof. intros A cs Hin. exact (proj1 (Forall_forall _ _) al_lits_main (A, cs) Hin). Qed.
  Ltac inlits := cbv beta delta [al_lits In map]; repeat (first [left; reflexivity | right]).
  (* [comment removed for export] *)
  Lemma al_lit_nth : forall i A cs, nth_error al_lits i = Some (A, cs) -> rw_cells asegs VM A cs.
  Proof. intros i A cs H. exact (al_lit A cs (nth_error_In al_lits i H)). Qed.
  Ltac al_idx A cs l :=
    lazymatch l with
    | (A, cs) :: _ => constr:(O)
    | _ :: ?t => let n := al_idx A cs t in constr:(S n)
    end.
  Ltac inlits_nth :=
    lazymatch goal with
    | |- rw_cells _ _ ?A ?cs =>
        let l := eval cbv delta [al_lits] in al_lits in
        let i := al_idx A cs l in
        exact (al_lit_nth i A cs (@eq_refl (option (Z * list cell)) (Some (A, cs))))
    end.
  (* [comment removed for export] *)
  Lemma in_releasems : rw_cells asegs VM (0x6a7298 + 40) [C4 (wz 0xffffffff); C4 (wz 0)].                      Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_premapped : rw_cells asegs VM (0x6a7298 + 56) [C8 (wz 0); C8 (wz 4096)].                             Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_ptrsize   : rw_cells asegs VM (0x6a7298 + 88) [C8 (wz 0x800000)].                                      Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_nreserved : rw_cells asegs VM (0x6a7298 + 112) [C8 (wz 0); C8 (wz 0); C8 (wz 0)].                     Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_secmutex  : rw_cells asegs VM (0x6a7298 + 680) [C8 (wz 0)].                                            Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_quar      : rw_cells asegs VM (0x6a7298 + 792) [C8 (wz 0x10000000); C8 (wz 0xE666661); C8 (wz 0x100000)]. Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_qmutex    : rw_cells asegs VM (0x6a7298 + 880) [C8 (wz 0)].                                            Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_gq        : rw_cells asegs VM (0x6a7298 + 888) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].         Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_fbmutex   : rw_cells asegs VM (0x6a7298 + 984) [C8 (wz 0)].                                            Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma in_maxuser   : rw_cells asegs VM (0x6a7298 + 3616) [C8 (wz (2 ^ 40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]].
  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  (* [comment removed for export] *)
  Lemma fl_fill      : rw_cells asegs VM (0x6a80f8 + 44) [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)].  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_psg       : rw_cells asegs VM (0x6a80f8 + 78) [C1 (b8 1)].                                Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_pp        : rw_cells asegs VM (0x6a80f8 + 85) [C1 (b8 1)].                                Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_ndtm      : rw_cells asegs VM (0x6a80f8 + 88) [C1 (b8 1)].                                Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_fastuw    : rw_cells asegs VM (0x73c428 + 34) [C1 (b8 1)].                                Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_csmt      : rw_cells asegs VM (0x73c428 + 120) [C8 (wz 0xffffffffffffffff)].                         Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_mmaplim   : rw_cells asegs VM (0x73c428 + 144) [C8 (wz 0)].                               Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_decorate  : rw_cells asegs VM (0x73c428 + 260) [C1 (b8 0)].                               Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_c219      : rw_cells asegs VM (0x73c428 + 219) [C1 (b8 1)].                               Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_c244      : rw_cells asegs VM (0x73c428 + 244) [C1 (b8 1)].                               Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_shbase    : rw_cells asegs VM 0x6aa8f8 [C8 (wz 0x7fff8000)].                               Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_highend   : rw_cells asegs VM 0x6ab5e0 [C8 (wz (2 ^ 47 - 1)); C8 (wz 0); C8 (wz 0)].       Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_canpoison : rw_cells asegs VM 0x6aa15c [C1 (b8 1)].                                         Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_inited    : rw_cells asegs VM 0x6ab5d8 [C1 (b8 1)].                                         Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_ctxsize   : rw_cells asegs VM 0x6ab5fc [C4 (wz 30)].                                        Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_tsdinit   : rw_cells asegs VM 0x6aa160 [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)].    Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_allocfl   : rw_cells asegs VM 0x72cb60 [C1 (b8 0); C1 (b8 1); C1 (b8 0)].                  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_iainit    : rw_cells asegs VM 0x73a388 [C1 (b8 0); C1 (b8 0); C2 (wz 0)].                  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_hooks     : rw_cells asegs VM 0x73c3c0 (repeat (C8 (wz 0)) 10).                             Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_dying     : rw_cells asegs VM 0x73c41c [C4 (wz 0)].                                         Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_realms    : rw_cells asegs VM 0x5eaa70 [C8 (wz 0x569e10)].                                  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_got       : rw_cells asegs VM 0x5e77f8 (map (fun v => C8 (wz v))
                         [0x73a3a0; 0x5eaaa8; 0x73c428; 0x6a80f8; 0x6aa8f8; 0x6ab5e8; 0x6ab5f0; 0x6ab5e0; 0x5eaa70; 0x5eaa68; 0x5eaaa0; 0x5eaab8; 1; 0x73c41c; 0x73a398]).
  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_pagesz    : rw_cells asegs VM 0x73a3a0 [C8 (wz 4096)].                                      Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_secname   : rw_cells asegs VM 0x5eaaa8 [C8 (wz 0x2ebe7)].                                   Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_primname  : rw_cells asegs VM 0x5eaab8 [C8 (wz 0x478d1)].                                   Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_tlsslot   : rw_cells asegs VM 0xbe1c38 [C8 (wz 0xc03038)].                                  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_lsandis   : rw_cells asegs VM 0xbe1cb0 [C4 (wz 0)].                                         Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fl_got2      : rw_cells asegs VM 0x5e8490 [C8 (wz 0x20)].                                      Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fx_libcpgsz  : rw_cells asegs VM 0xc01f50 [C8 (wz 4096)].                                      Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  Lemma fx_gotssp    : rw_cells asegs VM 0x5e9798 [C8 (wz 0xc01cd0)].                                  Proof. first [inlits_nth | apply al_lit; inlits]. Qed.
  (* [comment removed for export] *)
  Lemma fx_canary : exists gd : word, rw_cells asegs VM 0xc01cd0 [C8 gd].
  Proof.
    exists (edenot E (EVar 61)).
    pose proof (kword_main w_all (CAbs, 0xc01cd0) 8 (EVar 61) ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)) as W.
    revert W. pmc_simpl. rewrite Z.add_0_l. intros W.
    apply rw_cells_img; [cbn; tauto | lia | csz; lia |]. apply bytes_at_of_nth; [lia | csz; lia |]. intros i Hi.
    apply (rdn_mrd ASEGS (cells_bytes [C8 (edenot E (EVar 61))]) VM 0xc01cd0); [| lia | csz; lia | exact Hi].
    cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact (W ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma in_spacebeg : rw_cells asegs VM (0x6a7298 + 32) [C8 (wz (pm_space_beg X))].
  Proof.
    replace (pm_space_beg X) with (CXV (CRI, - 2 ^ 37)) by (pmc_simpl; unfold pm_region_info; lia).
    apply (img_word_main (0x6a7298 + 32) (CRI, - 2 ^ 37) ltac:(vm_cast_no_check (@eq_refl bool true))); lia.
  Qed.
  Lemma in_regioninfo : rw_cells asegs VM (0x6a7298 + 48) [C8 (wz (pm_region_info X))].
  Proof. replace (pm_region_info X) with (CXV (CRI, 0)) by (pmc_simpl; lia). apply (img_word_main (0x6a7298 + 48) (CRI, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.
  Lemma in_chunks : rw_cells asegs VM (0x6a7298 + 72) [C8 (wz (ps_b08 X))].
  Proof. replace (ps_b08 X) with (CXV (CB08, 0)) by (pmc_simpl; lia). apply (img_word_main (0x6a7298 + 72) (CB08, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.
  Lemma in_ptrbase : rw_cells asegs VM (0x6a7298 + 80) [C8 (wz (ps_b08 X))].
  Proof. replace (ps_b08 X) with (CXV (CB08, 0)) by (pmc_simpl; lia). apply (img_word_main (0x6a7298 + 80) (CB08, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.
  (* [comment removed for export] *)
  Lemma in_hdr : rw_cells asegs VM (0x6a7298 + 32)
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
  (* [comment removed for export] *)
  Lemma fl_tsd : rw_cells asegs VM 0xc03038 [C8 (wz (ps_b10 X))].
  Proof. replace (ps_b10 X) with (CXV (CB10, 0)) by (pmc_simpl; lia). apply (img_word_main 0xc03038 (CB10, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ia_zero_scan : AsanHexTree.zpt AsanUbsan_seg_bytes_003 (Z.to_N (0x6abb00 - 0x5ea000)) (Z.to_N 0x81030).
  Proof. exact AsPlanImagesHexZ.asan_ia_zero. Qed.   (* [comment removed for export] *)
  Lemma seg_rom_bss_ia : forall z, 0x6abb00 <= z < 0x72cb30 -> PropExec.seg_rom ASEGS (wa z) = Some (b8 0).
  Proof.
    intros z Hz. unfold PropExec.seg_rom, memory_read. rewrite wa_unsigned by lia. change (Z.of_N 1) with 1.
    replace (find_segment ASEGS z 1) with (Some AsanUbsan_segment_003).
    2:{ rewrite asan_segs_eq. cbn -[Z.leb Z.add Z.of_N]. cbn [Z.of_N seg_base seg_size AsanUbsan_segment_000 AsanUbsan_segment_001 AsanUbsan_segment_002 AsanUbsan_segment_003].
        destruct (Z.leb_spec 65536 z); destruct (Z.leb_spec (z + 1) (65536 + 1593344)); cbn [andb]; try lia;
        destruct (Z.leb_spec 1658880 z); destruct (Z.leb_spec (z + 1) (1658880 + 4046848)); cbn [andb]; try lia;
        destruct (Z.leb_spec 5705728 z); destruct (Z.leb_spec (z + 1) (5705728 + 495616)); cbn [andb]; try lia;
        destruct (Z.leb_spec 6201344 z); destruct (Z.leb_spec (z + 1) (6201344 + 6397952)); cbn [andb]; try lia. reflexivity. }
    replace (seg_readable AsanUbsan_segment_003) with true by reflexivity.
    cbn [seg_bytes seg_base N.to_nat Pos.to_nat Pos.iter_op segment_read_bytes AsanUbsan_segment_003].
    change (Z.of_N 6201344%N) with 6201344.
    cbn [AsanUbsan_segment_003 seg_bytes]. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
    match goal with |- context [segment_byte_at ?l ?o] => replace (segment_byte_at l o) with (Some (b8 0)); [reflexivity|] end.
    symmetry. eapply (AsanHexTree.segment_byte_at_zero_pt _ _ _ _ ia_zero_scan); [rewrite asan_len3; cbn; lia | lia].
  Qed.
  Lemma ia_pristine : forall z, 0x6abb00 <= z < 0x72cb30 -> VM (wa z) = None /\ mrd asegs VM (wa z) = Some (b8 0).
  Proof.
    intros z Hz. pose proof (pmc_img _ _ _ _ _ _ MC 0x6abb00 0x72cb30 ltac:(vm_cast_no_check (@eq_refl bool true)) z Hz) as HN. fold (wa z) in HN.
    rewrite (vm_img z ltac:(lia)). split; [exact HN|]. unfold mrd. rewrite (vm_img z ltac:(lia)), HN, seg_rom_lib, asegs_ASEGS. apply seg_rom_bss_ia. exact Hz.
  Qed.
  Lemma ia_main : u8arr asegs VM 0x6abb00 (repeat (b8 0) (Z.to_nat 0x81030)).
  Proof.
    split; [| rewrite repeat_length, Z2Nat.id by lia; apply img_wr; lia].
    apply bytes_at_of_nth; [lia | rewrite repeat_length, Z2Nat.id by lia; lia |]. intros i Hi. rewrite repeat_length in Hi.
    rewrite (nth_error_repeat (b8 0) Hi). apply (proj2 (ia_pristine (0x6abb00 + Z.of_nat i) ltac:(lia))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  Lemma th_tls : rw_cells asegs VM (T + 48) [C8 (wz 0xbe23c8); C8 (wz 0xbe24b4)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 48) [C8 (wz 0xbe23c8); C8 (wz 0xbe24b4)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_dtv : rw_cells asegs VM (T + 64) [C8 (wz 0xbe1ca8)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 64) [C8 (wz 0xbe1ca8)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_fs : rw_cells asegs VM (T + 72) [C8 (wz (ps_b16 X))].
  Proof. geoT. pose proof (obj_word_out (CB09, 72) (CB16, 0) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b09) as W. revert W. pmc_simpl. rewrite !Z.add_0_r. intros W. apply W; lia. Qed.
  Lemma th_zero80 : forall z, T + 80 <= z < T + 3168 -> VM (wa z) = Some (b8 0).
  Proof. geoT. pose proof (obj_zero_main (CB09, 80) 3088 _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) (fun z Hz => proj1 (vr_b09 z Hz))) as W. revert W. pmc_simpl. intros W z Hz. apply W; lia. Qed.
  Lemma th_unw : rw_cells asegs VM (T + 3168) [C1 (b8 0)].
  Proof. geoT. pose proof (obj_bytes_out (CB09, 3168) [C1 (b8 0)] _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b09) as W. revert W. pmc_simpl. csz. intros W. apply W; lia. Qed.
  Lemma th_zero3169 : forall z, T + 3169 <= z < T + 4096 -> VM (wa z) = Some (b8 0).
  Proof. geoT. pose proof (obj_zero_main (CB09, 3169) 927 _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) (fun z Hz => proj1 (vr_b09 z Hz))) as W. revert W. pmc_simpl. intros W z Hz. apply W; lia. Qed.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma athr_cells_main : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> athr_cells VM.
  Proof.
    intros HCEIL Hh'. pose proof (al_ceil HCEIL Hh') as AC. geoT.
    pose proof al_CTX as (C1' & C2 & C3 & C4' & C5). cbn [fst snd] in C1', C2, C3, C4', C5.
    pose proof al_D as (D1 & D2 & D3 & D4 & D5). cbn [fst snd] in D1, D2, D3, D4, D5.
    exists CTX, T, (ps_b12 X), (wz 0xbe23c8), (wz 0xbe24b4).
    split; [exact fl_tsd|]. split; [exact cx_thr|]. split; [exact th_tls|].
    split. { pose proof (img_word_main (ATP + 24) (CB12, 0) ltac:(vm_cast_no_check (@eq_refl bool true))) as W. revert W. pmc_simpl. rewrite Z.add_0_r. intros W. apply W; unfold ATP; lia. }
    split. { pose proof (obj_word_out (CB12, 24) (CAbs, ATP) _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) vr_b12) as W. revert W. pmc_simpl. rewrite Z.add_0_l. intros W. apply W; unfold ATP; lia. }
    rewrite AC. lia.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Notation VMM := (m_vmmaps model).
  #[local] Notation PMo := (PM_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
  Lemma ak_limit : vm_limit VMM = target_alloc_limit.
  Proof. exact (pm_limit _ _ _ _ _ PMo). Qed.
  Lemma ak_top : alloc_top VMM = sp0z - 8388608.
  Proof. pose proof (pm_topz _ _ _ _ _ PMo) as T0. cbn [cfg_model cfg_of] in T0. unfold TOP, pm_top in T0. exact T0. Qed.
  Lemma ak_eager : eager_used model <= 16838656.
  Proof. exact (pm_eager _ _ _ _ _ PMo). Qed.
  Lemma ak_reserved : vm_reserved VMM = segments_reserved ASEGS.
  Proof. exact (pm_reserved _ _ _ _ _ PMo). Qed.
  Lemma ak_res_list : segments_reserved ASEGS =
    [(Z_to_bv 64 0x10000, Z_to_bv 64 0x185000); (Z_to_bv 64 0x195000, Z_to_bv 64 0x3dc000); (Z_to_bv 64 0x571000, Z_to_bv 64 0x79000); (Z_to_bv 64 0x5ea000, Z_to_bv 64 0x61a000)].
  Proof. vm_compute. reflexivity. Qed.
  Lemma ak_maps : vm_maps VMM = zz2ww (PM_MAPS brk0z X).        Proof. exact PM_maps_eq. Qed.
  Lemma ak_noacc : vm_noaccess VMM = zz2ww (PM_NOACC brk0z X).  Proof. exact PM_noacc_eq. Qed.
  Lemma ak_lazy : m_vm_lazy model = zz2ww (PM_LAZY sp0z X).       Proof. exact PM_lazy_eq. Qed.
  (* [comment removed for export] *)
  Lemma ak1 : forall e, In e (vm_reserved VMM) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= 0xc04000.
  Proof. intros e He. rewrite ak_reserved in He. pose proof (proj1 (Forall_forall _ _) asan_res_hull e He) as [_ H2]. cbn [img_hi ASAN_H] in H2. exact H2. Qed.
  Lemma ak1_lo : forall e, In e (vm_reserved VMM) -> 0x10000 <= bv_unsigned (fst e).
  Proof. intros e He. rewrite ak_reserved in He. pose proof (proj1 (Forall_forall _ _) asan_res_hull e He) as [H1 _]. cbn [img_lo ASAN_H] in H1. exact H1. Qed.
  Lemma ak9 : forall x : word, 0x10000 <= bv_unsigned x < 0xc04000 -> in_rangesb x (vm_reserved VMM) = true.
  Proof.
    intros x Hx. rewrite ak_reserved. destruct (proj2 asan_res_cover (bv_unsigned x) ltac:(cbn [img_lo img_hi ASAN_H]; lia)) as [iv [Hin Hr]].
    unfold in_rangesb. apply existsb_exists. exists iv. split; [exact Hin|]. unfold zin_rangeb. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
       (pm_meta_map brk0z X <= bv_unsigned x < pm_meta_map brk0z X + 4096)                        (* [comment removed for export] *)
    \/ (ps_b08 X <= bv_unsigned x < ps_b08 X + 0x800000)                                        (* [comment removed for export] *)
    \/ (ps_b06 X <= bv_unsigned x < pm_region_info X)                                           (* [comment removed for export] *)
    \/ (pm_region_info X + 4096 <= bv_unsigned x < ps_b06 X + 0x2000011000)                     (* [comment removed for export] *)
    \/ (0x8fff7000 <= bv_unsigned x < 0x2008fff7000).                                           (* [comment removed for export] *)
  Proof.
    intros x Hx. rewrite ak_noacc in Hx. destruct (zz_cases _ _ zz_ok_noacc Hx) as [p [Hp Hr]].
    unfold PM_NOACC, PM_REM in Hp. rewrite !in_app_iff in Hp. cbn [In] in Hp.
    destruct Hp as [[<-|[<-|[<-|[]]]]|[Hp|[<-|[]]]]; cbn [fst snd] in Hr; try lia.
    destruct (pm_region_info X + 4096 <? ps_b06 X + 0x2000011000) eqn:C; cbn [In] in Hp; [|tauto].
    destruct Hp as [<-|[]]. cbn [fst snd] in Hr. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma al_AE : 0x7fff8000 + page_down sp0z / 8 <= 0x10007fff8000.
  Proof.
    pose proof lz_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VSP). pose proof pd_facts as (PD1 & PD2 & PD3).
    assert (page_down sp0z / 8 <= 0x800000000000 / 8) by (apply Z.div_le_mono; lia). lia.
  Qed.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Lemma ak8a : forall x, 0x7fff7000 <= bv_unsigned x < 0x10007fff8000 -> in_rangesb x (vm_maps VMM) = true.
  Proof.
    intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) 0x8fff7000); [| destruct (Z_lt_le_dec (bv_unsigned x) 0x2008fff7000)].
    - apply (ak_maps_in 0x7fff7000 0x10000000); [unfold PM_MAPS; cbn [In]; tauto | lia].
    - apply (ak_maps_in 0x8fff7000 0x20000000000); [unfold PM_MAPS; cbn [In]; tauto | lia].
    - apply (ak_maps_in 0x2008fff7000 0xdfff0001000); [unfold PM_MAPS; cbn [In]; tauto | lia].
  Qed.
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Lemma ak_sh_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> sh aceil + 4096 <= 0x10007fff8000 /\ sh AsShadow.AHI_LO = 0x2008fff7000.
  Proof.
    intros HCEIL Hh'. pose proof (al_ceil HCEIL Hh') as AC. pose proof al_AE as AE4. pose proof pd_facts as (PD1 & PD2 & PD3).
    unfold sh. rewrite AC. unfold AsShadow.AHI_LO, ASHADOW_BASE. split; [| reflexivity].
    replace (page_down sp0z - 8388608) with (page_down sp0z + (-1048576) * 8) by lia. rewrite Z.div_add by lia. lia.
  Qed.
  Lemma ak3_hish : forall x, sh AsShadow.AHI_LO <= bv_unsigned x < AsShadow.AHI_LO -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. unfold sh, AsShadow.AHI_LO, ASHADOW_BASE in Hx. apply ak8a. lia. Qed.
  Lemma ak4_hish_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    forall a n, sh AsShadow.AHI_LO <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh aceil -> map_contains (vm_maps VMM) a n = true.
  Proof.
    intros HCEIL Hh' a n H0 H1 H2. pose proof (ak_sh_ceil HCEIL Hh') as [S1 S2].
    rewrite S2 in H0. apply ak4_hish; lia.
  Qed.
  Lemma ak5_hish_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    forall x, sh AsShadow.AHI_LO <= bv_unsigned x < sh aceil -> in_rangesb x (zz2ww (PM_ZR sp0z X)) = true /\ in_rangesb x (zz2ww (PM_LAZY sp0z X)) = true.
  Proof. intros HCEIL Hh' x Hx. pose proof (ak_sh_ceil HCEIL Hh') as [S1 S2]. rewrite S2 in Hx. apply ak5_hish. lia. Qed.
  Lemma ak8a_sh : forall x, AsShadow.ALOWSH_LO <= bv_unsigned x < AsShadow.AHI_LO -> in_rangesb x (vm_maps VMM) = true.
  Proof. intros x Hx. unfold AsShadow.AHI_LO, AsShadow.ALOWSH_LO in Hx. apply ak8a. lia. Qed.
  Lemma ak8b_sh : forall a n, sh ASegs.AIMG_TOP <= bv_unsigned a -> 0 < bv_unsigned n -> bv_unsigned a + bv_unsigned n <= sh AsShadow.ALOWSH_LO -> map_contains (vm_maps VMM) a n = true.
  Proof. intros a n H0 H1 H2. unfold sh, ASegs.AIMG_TOP, AsShadow.ALOWSH_LO, ASHADOW_BASE in *. apply ak4_losh; lia. Qed.
  Lemma ak8c_sh : forall x, sh ASegs.AIMG_TOP <= bv_unsigned x < sh AsShadow.ALOWSH_LO ->
    in_rangesb x (zz2ww (PM_ZR sp0z X)) = true /\ in_rangesb x (zz2ww (PM_LAZY sp0z X)) = true.
  Proof. intros x Hx. unfold sh, ASegs.AIMG_TOP, AsShadow.ALOWSH_LO, ASHADOW_BASE in Hx. apply ak8c. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ak_budget : eager_used model <= 16838656 /\ vm_limit VMM = target_alloc_limit /\ pages_total (zz2ww (PM_S sp0z brk0z X)) <= PM_S_PAGES /\ PM_S_PAGES = 69100.
  Proof. split; [exact ak_eager|]. split; [exact ak_limit|]. split; [exact (AsMainLazy.pages_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) | reflexivity]. Qed.
End AT_MAIN.
