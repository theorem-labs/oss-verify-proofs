(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the start-up invariant over the run's whole input with its mmap base; stack_present stated from sp0 - 6144512 to the stack top and re-proved as text, above sp0 from the start-up invariant's presence field; the lemmas above sp0 it no longer needs removed). *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan BothImages BothPlanImages AsHSTab BoStartupHSF AsMainVM BoMainState BoMainFacts BoMainLazyChk BoMainLazy BoMainCells BoMainIface BoMainIfacePre LazyRestrict LazySR.
From OSSVerify.boost_beast.http_request.images Require AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanInitL.
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
  Hypothesis HC : cs_ok BSEGS2 BOTH_H AsanInit.LIMIT
                        (SINV0L BPH2 OSSVerify.boost_beast.http_request.images.AsanUbsan.M.init_pc sp0 rdraw brk0 inp)
                        (argH0 sp0 rdraw inp) (in_fs inp) E ch R FULL model.
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
  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  #[local] Notation MR := (Mr BOTH_H (argH0 sp0 rdraw inp) E ch model FULL).
  #[local] Notation HID := (hid BOTH_H (argH0 sp0 rdraw inp) E ch model).
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].


  (* [comment removed for export] *)
  (* LPS 727298f3: the bounds of AS_InstDefs.ISPRES at main (AS_InstMainHeap's VM_SPRES): from
     sp0z - 8388608 + 2244096 = sp0z - 6144512, inside the zero window under sp0 (BoMainIfacePre.stack_full),
     to pm_stack_top sp0z: above sp0 the launch block, whose presence the start-up invariant carries to
     main (AsanPlanSound.co_pres, with TOP model = sp0z - 8388608). *)
  Theorem stack_present : forall z, sp0z - 8388608 + 2244096 <= z < pm_stack_top sp0z -> wview bsegs VM (wa z) <> None.
  Proof using sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC.   (* the argument list AS_InstanceKit applies *)
    intros z Hz. pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    assert (TB : pm_stack_top sp0z <= sp0z + 4096)
      by (unfold pm_stack_top, OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.page_up; Z.div_mod_to_equations; lia).
    assert (FZ : FULL (wa z) <> None).
    { destruct (Z_lt_le_dec z sp0z) as [LT|GE].
      - destruct (BoMainIfacePre.stack_full sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC z ltac:(lia)) as [b Hb].
        rewrite Hb. discriminate.
      - pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)
          as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TOPm & _).
        pose proof (co_pres _ _ _ _ _ _ _ _ _ _ _ HC) as P. unfold pres_ok, pres_hi in P.
        refine (P (wa z) _). rewrite TOPm, wa_unsigned by lia.
        unfold pm_stack_top, OSSVerify.Proofs.boost_beast.http_request.lib.Bo.AsMainSyms.page_up in Hz.
        split; [lia|]. Z.div_mod_to_equations. lia. }
    unfold wview. rewrite (vm_stack z) by (unfold page_down; Z.div_mod_to_equations; lia).
    destruct (FULL (wa z)) as [b|] eqn:Hb; [discriminate | exfalso; exact (FZ eq_refl)].
  Qed.
End AT_MAIN.
