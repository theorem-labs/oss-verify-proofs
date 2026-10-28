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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0 FakeStackRep.
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
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  Lemma fs_geom : 12599296 <= ps_b16 X /\ ps_b16 X + AFS_SIZE <= page_down sp0z - 8388608 /\ ps_b16 X mod 4096 = 0
                  /\ (ps_b16 X + AFS_SIZE <= 2147446784 \/ 17594333495296 <= ps_b16 X).
  Proof.
    pose proof (kp_facts _ _ kp_b16) as (A & B & C & D & F). cbn [fst snd] in A, B, C, D, F. unfold AFS_SIZE. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fs_geom_ceil : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 ->
    ASegs.AIMG_TOP <= ps_b16 X /\ ps_b16 X + AFS_SIZE <= aceil /\ ps_b16 X mod 4096 = 0 /\ aapp (ps_b16 X) AFS_SIZE.
  Proof.
    intros HCEIL Hh'. pose proof fs_geom as (G1 & G2 & G3 & G4). pose proof pd_facts as (PD1 & PD2 & PD3).
    assert (AC : aceil = page_down sp0z - 8388608) by (unfold aceil; rewrite Hh'; unfold AsMainSyms.page_down in *; lia).
    unfold aapp, aapp_lo, aapp_hi, ASegs.AIMG_TOP, AsShadow.ALOWSH_LO, AsShadow.AHI_LO. rewrite AC. unfold AFS_SIZE in *. lia.
  Qed.

  Lemma fs_tls : rw_cells asegs VM ATP [C8 (wz (ps_b16 X))].
  Proof.
    unfold ATP. replace (ps_b16 X) with (CXV (CB16, 0)) by (pmc_simpl; lia).
    apply (img_word_main 0xbe1c90 (CB16, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia.
  Qed.

  Lemma fs_hdr : rw_cells asegs VM (ps_b16 X)
    [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 20); C1 (b8 0)].
  Proof.
    pose proof fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE in G2.
    pose proof (obj_bytes_main (CB16, 0) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 20); C1 (b8 0)]
                  _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b16) as W.
    revert W. pmc_simpl. csz. rewrite Z.add_0_r. intros W. apply W; lia.
  Qed.

  Lemma fs_flags : forall a, ps_b16 X + AFS_FLAGS <= a < ps_b16 X + AFS_HDR -> rw_cells asegs VM a [C1 (b8 0)].
  Proof.
    intros a Ha. pose proof fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in G2, Ha.
    apply rw_cells_above; [cbn; tauto | lia | csz; lia |].
    apply bytes_at_of_nth; [lia | csz; lia |]. intros i Hi. cbv [cells_bytes cbytes app length] in Hi. destruct i as [|i]; [|lia]. cbn [cells_bytes cbytes app nth_error]. rewrite Z.add_0_r.
    unfold mrd. erewrite (zero_main w_all (CB16, 4096) 32768 ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)); [reflexivity | | revert Ha; pmc_simpl; lia].
    intros z Hz. apply (vm_obj _ _ z kp_b16); [lia | lia | lia |]. revert Hz. pmc_simpl. cbn [fst snd]. lia.
  Qed.

  Lemma fs_frames : stk asegs VM (ps_b16 X + AFS_HDR) (ps_b16 X + AFS_SIZE).
  Proof.
    pose proof fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in *.
    apply stk_of_some; [lia | lia |]. intros a Ha. exists (b8 0).
    apply (zero_main w_all (CB16, 36864) 11534336 ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)); [| revert Ha; pmc_simpl; lia].
    intros z Hz. apply (vm_obj _ _ z kp_b16); [lia | lia | lia |]. revert Hz. pmc_simpl. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_shadow_zero : forall z, SHOFF + ps_b16 X / 8 <= z < SHOFF + (ps_b16 X + AFS_SIZE) / 8 -> VM (wa z) = Some (b8 0).
  Proof.
    pose proof fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE in *. intros z Hz.
    apply (zero_main w_all (CSH16, 0) 1446400 ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)); [| revert Hz; pmc_simpl; unfold pm_sh, SHOFF; lia].
    intros y Hy. revert Hy. pmc_simpl. unfold pm_sh. intros Hy.
    replace y with (SHOFF + (8 * (y - SHOFF)) / 8) by (unfold SHOFF; lia).
    apply (vm_sw (ps_b16 X) 0xb09000); [| lia | unfold SHOFF in *; lia | lia | replace (ps_b16 X + 11571200) with ((ps_b16 X / 8 + 1446400) * 8) by lia; apply Z_mod_mult].
    unfold VISZ, VISZ0. apply in_or_app. left. cbn [In]. do 9 right. left. reflexivity.
  Qed.
  Lemma fs_shadow : stk asegs VM (sh (ps_b16 X)) (sh (ps_b16 X + AFS_SIZE)).
  Proof.
    pose proof fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE in *. unfold sh. rewrite ASHADOW_BASE_val. fold SHOFF.
    apply stk_of_some; [unfold SHOFF; lia | unfold SHOFF; lia |]. intros a Ha. exists (b8 0). apply fs_shadow_zero. unfold AFS_SIZE. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fs_main : forall (HCEIL : HeapCeil), hceil = sp0z - 8388608 -> RFSI (ps_b16 X) [] VM.
  Proof.
    intros HCEIL Hh'. pose proof (fs_geom_ceil HCEIL Hh') as (G1 & G2 & G3 & G4).
    apply RFSI_init; [exact G1 | exact G2 | exact G3 | exact G4 | exact fs_tls | apply hdr_zero; exact fs_hdr | exact fs_flags | exact fs_frames | exact fs_shadow].
  Qed.
End AT_MAIN.
