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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsDepotInv.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsPlanImagesHex.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainIfaceDepotScan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsHSTab AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition pm_trace (sp0z : Z) : list Z := if pm_short sp0z then [0x1a531c] else [0x1a531c; 0x1a666c].
Definition pm_trace_hash (sp0z : Z) : Z := if pm_short sp0z then 0x44c28bc02f9dd5cc else 0xe8e20d58505dc047.
Definition pm_nframes (sp0z : Z) : Z := if pm_short sp0z then 2 else 3.          (* [comment removed for export] *)
Definition pm_tab_slot (sp0z : Z) : Z := if pm_short sp0z then 11542280 else 11520244.   (* [comment removed for export] *)
(* [comment removed for export] *)
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
  Ltac cszl := rewrite ?length_cellsZ in * by (cbn; tauto); csz.

  Lemma kp_b21f : 12599296 <= ps_b21 X /\ ps_b21 X + 0x100000 <= page_down sp0z - 8388608 /\ ps_b21 X mod 4096 = 0.
  Proof. pose proof (kp_facts _ _ kp_b21) as (A & B & C & D & _). cbn [fst snd] in A, B, C, D. lia. Qed.
  Lemma kp_b22f : 12599296 <= ps_b22 X /\ ps_b22 X + 0x800000 <= page_down sp0z - 8388608 /\ ps_b22 X mod 4096 = 0.
  Proof. pose proof (kp_facts _ _ kp_b22) as (A & B & C & D & _). cbn [fst snd] in A, B, C, D. lia. Qed.

  (* [comment removed for export] *)
  Lemma vr_b22 : vrange (ps_b22 X) (ps_b22 X + 0x800000).
  Proof.
    intros z Hz. split; [exact (vm_b22 z Hz)|].
    right. left. split; [exact (zinP_of_In z _ (ps_b22 X, 0x800000) (nth_error_In (VISK sp0z brk0z X) 5 eq_refl) Hz)|].
    pose proof (kp_facts _ _ kp_b22) as (_ & PB1 & PB2 & PB3 & PB4).
    pose proof (kp_apart_ne 11 2 _ _ ltac:(lia) kp_b22 kp_b06) as A2. pose proof (kp_apart_ne 11 3 _ _ ltac:(lia) kp_b22 kp_b08) as A3. cbn [fst snd] in A2, A3.
    pose proof G_cases as GC. pose proof pd_facts as PD.
    destruct GC as [(Hg & HG & PBK)|(Hg & HG & PBK)].
    - pose proof (proj1 (Forall_forall _ _) (proj2 (pso_brk _ _ _ _ SOK Hg)) _ (nth_error_In _ _ kp_b22)) as A14. cbv beta in A14. cbn [fst snd] in A14.
      revert Hz A14; prepI; zlistsI; rewrite HG; zinP_norm2; intros Hz A14 HN. clear MC SOK. zcases HN; (first [clear - HN A14 Hz A3 REL A2 PB4; lia | lia]).
    - pose proof (kp_apart_ne 11 17 _ _ ltac:(lia) kp_b22 PBK) as A14. cbn [fst snd] in A14.
      revert Hz A14; prepI; zlistsI; rewrite HG; zinP_norm2; intros Hz A14 HN. clear MC SOK. zcases HN; (first [clear - HN A14 Hz A3 REL A2 PB4; lia | lia]).
  Qed.

  (* [comment removed for export] *)
  Lemma img_cells_w : forall (u : bool) A cs, pm_short sp0z = u ->
    cells_wfb cs = true -> 0x571000 <= A -> A + Z.of_nat (cells_size cs) <= 0xc04000 ->
    bytes_check_w (WS (Some u) None) (CAbs, A) (cellsZ cs) = true -> rw_cells asegs VM A cs.
  Proof.
    intros u A cs U WF H1 H2 HB. pose proof (cells_wfb_sound cs WF) as WF'.
    apply rw_cells_img; [exact WF' | lia | lia |]. rewrite <- map_b8_cellsZ.
    apply (bytes_main (WS (Some u) None) (CAbs, A) (cellsZ cs) HB (world_uw _ U)); pmc_simpl; rewrite ?(length_cellsZ cs WF'); [lia | lia | apply vr_img; lia].
  Qed.
  (* [comment removed for export] *)
  Lemma obj_cells_w : forall (u : bool) a cs lo hi, pm_short sp0z = u -> bytes_check_w (WS (Some u) None) a (cellsZ cs) = true -> cells_wfb cs = true ->
    vrange lo hi -> lo <= CXV a -> CXV a + Z.of_nat (cells_size cs) <= hi -> 0xc04000 <= lo -> hi <= 2 ^ 64 -> rw_cells asegs VM (CXV a) cs.
  Proof.
    intros u a cs lo hi U Hc WF VR H0 H1 H2 H3. apply cells_wfb_sound in WF. apply rw_cells_above; [exact WF | lia | lia |].
    rewrite <- map_b8_cellsZ. apply (bytes_main (WS (Some u) None) a (cellsZ cs) Hc (world_uw _ U)); rewrite ?(length_cellsZ cs WF); [lia | lia |].
    eapply vr_sub; [exact VR | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dp_nui : rw_cells asegs VM 12109784 [C4 (wz 1)].
  Proof. exact (img_cells_main 12109784 [C4 (wz 1)] ltac:(vm_compute; reflexivity)). Qed.
  Lemma dp_map1 : rw_cells asegs VM 12109800 [C8 (wz (ps_b21 X))].
  Proof. replace (ps_b21 X) with (CXV (CB21, 0)) by (pmc_simpl; lia). apply (img_word_main 12109800 (CB21, 0) ltac:(vm_compute; reflexivity)); lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma seg_rom_bss_tab : forall z, 7915480 <= z < 12109784 -> PropExec.seg_rom ASEGS (wa z) = Some (b8 0).
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
    symmetry. eapply (AsanHexTree.segment_byte_at_zero_pt _ _ _ _ AsMainIfaceDepotScan.tab_zero_scan); [rewrite asan_len3; cbn; lia | lia].
  Qed.
  (* [comment removed for export] *)
  Lemma dp_tab_pristine : forall lo hi z, img_check lo hi = true -> lo <= z < hi -> 7915480 <= lo -> hi <= 12109784 -> mrd asegs VM (wa z) = Some (b8 0).
  Proof.
    intros lo hi z Hc Hz H1 H2. pose proof (pmc_img _ _ _ _ _ _ MC lo hi Hc z Hz) as HN. fold (wa z) in HN.
    unfold mrd. rewrite (vm_img z ltac:(lia)), HN, seg_rom_lib, asegs_ASEGS. apply seg_rom_bss_tab. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma dp_half : forall S z, img_cells_check S [C4 (wz 0)] = true -> S <= z < S + 4 -> mrd asegs VM (wa z) = Some (b8 0).
  Proof.
    intros S z Hc Hz. pose proof (img_cells_main S [C4 (wz 0)] Hc) as [[_ (_ & _ & HB)] _].
    specialize (HB (Z.to_nat (z - S)) ltac:(change (length (cells_bytes [C4 (wz 0)])) with 4%nat; lia)).
    rewrite Z2Nat.id in HB by lia. replace (S + (z - S)) with z in HB by lia. rewrite HB.
    assert (Hn : (Z.to_nat (z - S) < 4)%nat) by lia.
    destruct (Z.to_nat (z - S)) as [|[|[|[|n]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia].
  Qed.
  Lemma dp_tab_zero4 : forall A, (7915480 <= A /\ A + 4 <= 11520244) \/ (11520248 <= A /\ A + 4 <= 11542280) \/ (11542284 <= A /\ A + 4 <= 12109784) ->
    rw_cells asegs VM A [C4 (wz 0)].
  Proof.
    intros A HA. apply rw_cells_img; [cbn; tauto | lia | csz; lia |].
    apply bytes_at_of_nth; [lia | change (length (cells_bytes [C4 (wz 0)])) with 4%nat; lia |]. intros i Hi.
    change (length (cells_bytes [C4 (wz 0)])) with 4%nat in Hi.
    assert (Hb : nth_error (cells_bytes [C4 (wz 0)]) i = Some (b8 0)) by (destruct i as [|[|[|[|i]]]]; [reflexivity | reflexivity | reflexivity | reflexivity | lia]).
    rewrite Hb.
    destruct HA as [HA|[HA|HA]].
    - destruct (Z_lt_ge_dec (A + Z.of_nat i) 11520240) as [Hlo|Hhi]; [apply (dp_tab_pristine 7915480 11520240); [vm_compute; reflexivity | lia | lia | lia] | apply (dp_half 11520240); [vm_compute; reflexivity | lia]].
    - apply (dp_tab_pristine 11520248 11542280); [vm_compute; reflexivity | lia | lia | lia].
    - destruct (Z_lt_ge_dec (A + Z.of_nat i) 11542288) as [Hlo|Hhi]; [apply (dp_half 11542284); [vm_compute; reflexivity | lia] | apply (dp_tab_pristine 11542288 12109784); [vm_compute; reflexivity | lia | lia | lia]].
  Qed.
  (* [comment removed for export] *)
  Lemma dp_tab_slots : rw_cells asegs VM 11542280 [C4 (wz (if pm_short sp0z then 1 else 0))] /\ rw_cells asegs VM 11520244 [C4 (wz (if pm_short sp0z then 0 else 1))].
  Proof.
    destruct (pm_short sp0z) eqn:U; split.
    - exact (img_cells_w true 11542280 [C4 (wz 1)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - exact (img_cells_w true 11520244 [C4 (wz 0)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - exact (img_cells_w false 11542280 [C4 (wz 0)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - exact (img_cells_w false 11520244 [C4 (wz 1)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
  Qed.
  (* [comment removed for export] *)
  Lemma buckets : bucket 0x44c28bc02f9dd5cc = 906700 /\ bucket 0xe8e20d58505dc047 = 901191.
  Proof. split; reflexivity. Qed.
  Lemma dp_tab : forall b, 0 <= b < 2 ^ 20 -> rw_cells asegs VM (7915480 + 4 * b) [C4 (wz (hd 0 (d_chain (depot0 sp0z X) b)))].
  Proof.
    intros b Hb. pose proof dp_tab_slots as [S1 S2]. pose proof buckets as [BS BL]. cbn [depot0 d_chain]. unfold pm_trace_hash in *.
    destruct (pm_short sp0z); [rewrite BS | rewrite BL].
    - destruct (Z.eqb_spec b 906700) as [->|N1]; cbn [hd]; [change (7915480 + 4 * 906700) with 11542280; exact S1|].
      destruct (Z.eq_dec b 901191) as [->|N2]; [change (7915480 + 4 * 901191) with 11520244; exact S2|].
      apply dp_tab_zero4. lia.
    - destruct (Z.eqb_spec b 901191) as [->|N1]; cbn [hd]; [change (7915480 + 4 * 901191) with 11520244; exact S2|].
      destruct (Z.eq_dec b 906700) as [->|N2]; [change (7915480 + 4 * 906700) with 11542280; exact S1|].
      apply dp_tab_zero4. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dp_node1 : rw_cells asegs VM (ps_b21 X + 16) [C8 (wz (pm_trace_hash sp0z)); C4 (wz 0)] /\ rw_cells asegs VM (ps_b21 X + 28) [C4 (wz 1)].
  Proof.
    pose proof kp_b21f as (B1 & B2 & _). pose proof pd_facts as PD. unfold pm_trace_hash. destruct (pm_short sp0z) eqn:U; split.
    - pose proof (obj_cells_w true (CB21, 16) [C8 (wz 0x44c28bc02f9dd5cc); C4 (wz 0)] _ _ U ltac:(vm_compute; reflexivity) eq_refl vr_b21) as W.
      revert W. pmc_simpl. csz. intros W. apply W; lia.
    - pose proof (obj_cells_w true (CB21, 28) [C4 (wz 1)] _ _ U ltac:(vm_compute; reflexivity) eq_refl vr_b21) as W. revert W. pmc_simpl. csz. intros W. apply W; lia.
    - pose proof (obj_cells_w false (CB21, 16) [C8 (wz 0xe8e20d58505dc047); C4 (wz 0)] _ _ U ltac:(vm_compute; reflexivity) eq_refl vr_b21) as W.
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

  (* [comment removed for export] *)
  Lemma dp_store_hdr : rw_cells asegs VM 7849928 [C8 (wz (pm_nframes sp0z))] /\ rw_cells asegs VM 7849944 [C8 (wz (ps_b22 X))]
                       /\ rw_cells asegs VM 7849952 [C4 (wz (pm_nframes sp0z))].
  Proof.
    unfold pm_nframes. split; [|split].
    - destruct (pm_short sp0z) eqn:U.
      + exact (img_cells_w true 7849928 [C8 (wz 2)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
      + exact (img_cells_w false 7849928 [C8 (wz 3)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
    - replace (ps_b22 X) with (CXV (CB22, 0)) by (pmc_simpl; lia). apply (img_word_main 7849944 (CB22, 0) ltac:(vm_compute; reflexivity)); lia.
    - destruct (pm_short sp0z) eqn:U.
      + exact (img_cells_w true 7849952 [C4 (wz 2)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
      + exact (img_cells_w false 7849952 [C4 (wz 3)] U eq_refl ltac:(lia) ltac:(csz; lia) ltac:(vm_compute; reflexivity)).
  Qed.

  (* [comment removed for export] *)
  Lemma dp_store_zero : forall z, ps_b22 X + 8 * pm_nframes sp0z <= z < ps_b22 X + 0x100000 -> VM (wa z) = Some (b8 0).
  Proof.
    pose proof kp_b22f as (B1 & B2 & _). pose proof pd_facts as PD. unfold pm_nframes.
    destruct (pm_short sp0z) eqn:U; intros z Hz.
    - apply (zero_main (WS (Some true) None) (CB22, 16) (0x100000 - 16) ltac:(vm_compute; reflexivity) (world_uw _ U) ltac:(lia)); [|revert Hz; pmc_simpl; lia].
      intros y Hy. apply vm_b22. revert Hy. pmc_simpl. lia.
    - apply (zero_main (WS (Some false) None) (CB22, 24) (0x100000 - 24) ltac:(vm_compute; reflexivity) (world_uw _ U) ltac:(lia)); [|revert Hz; pmc_simpl; lia].
      intros y Hy. apply vm_b22. revert Hy. pmc_simpl. lia.
  Qed.
  Lemma dp_space : exists junk, u8arr asegs VM (ps_b22 X + 8 * pm_nframes sp0z) junk /\ Z.of_nat (length junk) = 8 * (131072 - pm_nframes sp0z).
  Proof.
    pose proof kp_b22f as (B1 & B2 & _). pose proof pd_facts as PD.
    assert (NF : 2 <= pm_nframes sp0z <= 3) by (unfold pm_nframes; destruct (pm_short sp0z); lia).
    exists (repeat (b8 0) (Z.to_nat (8 * (131072 - pm_nframes sp0z)))). split; [| rewrite repeat_length; lia].
    apply u8arr_constZ; [lia | lia | lia |]. intros z Hz. apply dp_store_zero. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem depot_main : DEPOT asegs (depot0 sp0z X) VM.
  Proof.
    pose proof kp_b21f as (B1 & B2 & _). pose proof kp_b22f as (C1 & C2 & _). pose proof pd_facts as PD.
    pose proof (kp_apart 10 11 _ _ ltac:(lia) kp_b21 kp_b22) as A. cbn [fst snd] in A.
    assert (NF : 2 <= pm_nframes sp0z <= 3) by (unfold pm_nframes; destruct (pm_short sp0z); lia).
    assert (HH : 0 <= pm_trace_hash sp0z < 2 ^ 64) by (unfold pm_trace_hash; destruct (pm_short sp0z); lia).
    pose proof (bucket_range (pm_trace_hash sp0z)) as BR.
    split.
    - (* [comment removed for export] *) constructor; cbn [depot0 d_ids d_frames d_hash d_chain d_nb d_sb]; unfold ASegs.AIMG_TOP.
      + lia.
      + lia.
      + intros id Hid. lia.
      + intros id Hid. rewrite Z.eqb_refl. left. lia.
      + intros b id Hin. destruct (Z.eqb_spec b (bucket (pm_trace_hash sp0z))) as [->|NE]; [|destruct Hin]. destruct Hin as [<-|[]]. split; [lia | reflexivity].
      + intros b. destruct (b =? bucket (pm_trace_hash sp0z)); [repeat constructor; cbn; tauto | constructor].
      + lia.
      + lia.
      + lia.
    - (* [comment removed for export] *) pose proof dp_node1 as [N1 N2]. pose proof dp_store_hdr as (S1 & S2 & S3).
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
