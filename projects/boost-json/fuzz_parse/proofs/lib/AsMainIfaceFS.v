(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsStack0 FakeStackRep.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan
  AsImages AsPlanImages AsHSTab AsStartupHSF AsMainVM AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsMainSyms.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsMainSyms~~~~~~06ps_b1669OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainFacts~~~~~~k83Xofk8chole_granted46Stdlib6ZArith6BinInt1Zpb2le37Corelib4Init5Logicr83and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~t28AFS_SIZEpb3addr82eqr82or37Corelib7Numbers7BinNumshia4Nposhia1Z09page_downpb6modulopb3sub35stdpp9bitvectorbdefinitionshmabbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hp68AIMG_TOP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~htd4aapphtd5aceil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~iic8HeapCeiliic5hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~inc4cell37Corelib4Init9Datatypesis04consis03nilhp65asegst23ATP69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainIface~~~~~~iv67pm_vmeminc2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jk58rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~joc2wzinc2C1joc2b8t29AFS_FLAGSt27AFS_HDRpb2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jv43stk69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAsMainLazy~~~~~~kj75SHOFFpb3divhma2bvis04Someis06option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kpb2wahtd2sht26fframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscFakeStackRep~~~~~~kua4RFSI3h5LinuxProcessSemanticsfLinuxProcessSem3Runlj48valid_splj49valid_brk69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~ln95ASEGSlj4avalid_argv3h5LinuxProcessSemanticsfLinuxProcessSem5Statelsf7in_argvlj4avalid_envplsf7in_envplj4h0entry_stack_fits79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~mj63acs69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSF~~~~~~mnb8HSF_asanlsf8in_hwcaplsf6in_uidln93APHlsf5in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~muc6ASAN_H69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~nj15LIMITnj15SINV0nj15argH079OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~no75cs_ok" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : ltac2:(zQ "10!lm0@1$0?3sp0").
  Hypothesis Vbrk : ltac2:(zQ "20!lmc!lr8@2$0$1?4brk0").
  Hypothesis Vav : ltac2:(zQ "20!ls1!lvd@1$0@1$1?3inp").
  Hypothesis Vev : ltac2:(zQ "20!mg8!mh6@1$0@1$1?3inp").
  Hypothesis Vfit : ltac2:(zQ "30!mi1!lvd!mh6@3$0?3sp0@1$1?3inp@1$2?3inp").
  Hypothesis Hh : ltac2:(zQ "50!mn4!ko9!kp1!hi0!mra@3$3@1$2$0@1$4?1h@2$1$0?2ch").
  Hypothesis HC : ltac2:(zQ "c0!lvd!mh6!ms6!mt2!mtc!mu3!ni7!lr8!nmc!nn5!nne!nsb@b$b$7$6$8@8$9$4?3sp0?5rdraw?4brk0@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@7$a$4?3sp0?5rdraw@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@1$5?3inp?1E?2ch?1R?4FULL?5model").
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

  Lemma fs_geom : ltac2:(zQ "f1!k0!o6!oc!r3!sc!hgf!hha!hi0!hi5!hk3!hkb!hl0!hlb!hm4!ho7&@2$6@1$0@2$1@1$2?1h?1E$5@2$4@2$3+nhmgg0@1$0@2$1@1$2?1h?1E@2$4@2$3~0@2$d@1$b@2$e@1$9#k0?3sp0+ogggg0@2$4@3$7$a@2$c@1$0@2$1@1$2?1h?1E+hgg0Z@2$8@2$3~0+nvvvngg0@2$3+hgggnvvvogg0@1$0@2$1@1$2?1h?1E").
  Proof.
    pose proof (kp_facts _ _ kp_b16) as (A & B & C & D & F). cbn [fst snd] in A, B, C, D, F. unfold AFS_SIZE. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fs_geom_ceil : ltac2:(zQ "h20!k0!o6!oc!sc!hi0!hkb!hgf!r3!hk3!ht1!ihb!ii3!im7!in3!hha!hlb!hm4!ho7>5HCEIL$c>0@3$4$5@1$d^1@2$h0@2$h1@1$8#k0?3sp0+ogggg0@2$3@2$7$9@1$0@2$1@1$2?1h?1E@2$3@2$7@2$e@1$0@2$1@1$2?1h?1E$6@1$b^2@2$3@3$4$5@2$f@1$0@2$1@1$2?1h?1E+hgg0Z@3$a^2@1$0@2$1@1$2?1h?1E$6").
  Proof.
    intros HCEIL Hh'. npose fs_geom as (G1 & G2 & G3 & G4). npose pd_facts as (PD1 & PD2 & PD3).
    assert (AC : aceil = page_down sp0z - 8388608) by (unfold aceil; rewrite Hh'; unfold AsMainSyms.page_down in *; lia).
    unfold aapp, aapp_lo, aapp_hi, ASegs.AIMG_TOP, AsShadow.ALOWSH_LO, AsShadow.AHI_LO. rewrite AC. unfold AFS_SIZE in *. lia.
  Qed.

  Lemma fs_tls : ltac2:(zQ "e0!hk3!o6!oc!ir8!ho7!it8!iu0!iu7!iv0!k0!jj4!jjf!jo0!js7@4$c$7@4$a@2$4@1$0#k0?3sp0@2$4@1$0#k0?4brk0@2$1@1$2?1h?1E?4FULL$8@3$5$3@1$b@1$d@1$9@2$1@1$2?1h?1E@1$6$3").
  Proof.
    unfold ATP. replace (ps_b16 X) with (CXV (CB16, 0)) by (pmc_simpl; lia).
    apply (img_word_main 0x6f43d8 (CB16, 0) ltac:(vm_cast_no_check (@eq_refl bool true))); lia.
  Qed.

  Lemma fs_hdr : ltac2:(zQ "f0!ir8!it8!jjf!js7!hk3!o6!oc!ho7!iu0!iu7!k0!jj4!jsd!jo0!jt3@4$d$9@4$b@2$7@1$4#k0?3sp0@2$7@1$4#k0?4brk0@2$5@1$6?1h?1E?4FULL@1$a@2$5@1$6?1h?1E@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3Z@3$1$0@1$2@1$3+h4@3$1$0@1$c@1$eZ@1$8$0").
  Proof.
    npose fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE in G2.
    pose proof (obj_bytes_main (CB16, 0) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 20); C1 (b8 0)]
                  _ _ ltac:(vm_cast_no_check (@eq_refl bool true)) eq_refl vr_b16) as W.
    revert W. pmc_simpl. csz. rewrite Z.add_0_r. intros W. apply W; lia.
  Qed.

  Lemma fs_flags : ltac2:(zQ "h40!o6!oc!hk3!k0!ir8!hha!ho7!it8!iu0!sc!hkb!iu7!jt9!ju5!jj4!jsd!jo0!jt3!r3!juf>1a$a>0@2$9@2$h2@2$5@1$3@2$0@1$1?1h?1E$c^1@2$h3^1@2$5@1$3@2$0@1$1?1h?1E$d@4$h0$b@4$e@2$6@1$2#k0?3sp0@2$6@1$2#k0?4brk0@2$0@1$1?1h?1E?4FULL^2@3$7$4@1$f@1$h1Z@1$8$4").
  Proof.
    intros a Ha. npose fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in G2, Ha.
    apply rw_cells_above; [cbn; tauto | lia | csz; lia |].
    apply bytes_at_of_nth; [lia | csz; lia |]. intros i Hi. cbv [cells_bytes cbytes app length] in Hi. destruct i as [|i]; [|lia]. cbn [cells_bytes cbytes app nth_error]. rewrite Z.add_0_r.
    unfold mrd. erewrite (zero_main w_all (CB16, 4096) 32768 ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)); [reflexivity | | revert Ha; pmc_simpl; lia].
    intros z Hz. apply (vm_obj _ _ z kp_b16); [lia | lia | lia |]. revert Hz. pmc_simpl. cbn [fst snd]. lia.
  Qed.

  Lemma fs_frames : ltac2:(zQ "b0!o6!oc!hk3!k0!hha!ho7!iu7!ju5!hgf!jj4!kj0@4$a$6@4$9@2$5@1$2#k0?3sp0@2$5@1$2#k0?4brk0@2$0@1$1?1h?1E?4FULL@2$4@1$3@2$0@1$1?1h?1E$7@2$4@1$3@2$0@1$1?1h?1E$8").
  Proof.
    npose fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE, AFS_FLAGS, AFS_HDR in *.
    apply stk_of_some; [lia | lia |]. intros a Ha. exists (b8 0).
    apply (zero_main w_all (CB16, 36864) 11534336 ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)); [| revert Ha; pmc_simpl; lia].
    intros z Hz. apply (vm_obj _ _ z kp_b16); [lia | lia | lia |]. revert Hz. pmc_simpl. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fs_shadow_zero : ltac2:(zQ "h40!hk3!o6!oc!hha!k0!kn4!knd!ko3!ho7!ko9!kp1!sc!hi0!hkb!hgf!jj4!kt5!jt3!r3!juf>1z$d>0@2$b@2$h2@2$3$5@2$6@1$4@2$1@1$2?1h?1E+8^1@2$h3^1@2$3$5@2$6@2$3@1$4@2$1@1$2?1h?1E$e+8@3$c@1$a@1$7@1$0#8@5$f@2$8@1$0#k0?3sp0@2$8@1$0#k0?4brk0@2$1@1$2?1h?1E?4FULL@1$h0^2@2$9@1$7@1$0#8@1$h1Z").
  Proof.
    npose fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE in *. intros z Hz.
    apply (zero_main w_all (CSH16, 0) 1446400 ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)); [| revert Hz; pmc_simpl; unfold pm_sh, SHOFF; lia].
    intros y Hy. revert Hy. pmc_simpl. unfold pm_sh. intros Hy.
    replace y with (SHOFF + (8 * (y - SHOFF)) / 8) by (unfold SHOFF; lia).
    apply (vm_sw (ps_b16 X) 0xb09000); [| lia | unfold SHOFF in *; lia | lia | replace (ps_b16 X + 11571200) with ((ps_b16 X / 8 + 1446400) * 8) by lia; apply Z_mod_mult].
    unfold VISZ, VISZ0. apply in_or_app. left. cbn [In]. do 7 right. left. reflexivity.   (* [comment removed for export] *)
  Qed.
  Lemma fs_shadow : ltac2:(zQ "b0!o6!oc!hk3!k0!ktb!ho7!iu7!hgf!jj4!kj0!hha@4$9$6@4$8@2$5@1$2#k0?3sp0@2$5@1$2#k0?4brk0@2$0@1$1?1h?1E?4FULL@1$4@1$3@2$0@1$1?1h?1E@1$4@2$a@1$3@2$0@1$1?1h?1E$7").
  Proof.
    npose fs_geom as (G1 & G2 & G3 & _). pose proof pd_facts as PD. unfold AFS_SIZE in *. unfold sh. rewrite ASHADOW_BASE_val. fold SHOFF.
    apply stk_of_some; [unfold SHOFF; lia | unfold SHOFF; lia |]. intros a Ha. exists (b8 0). apply fs_shadow_zero. unfold AFS_SIZE. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem fs_main : ltac2:(zQ "e0!hk3!ho7!o6!oc!iu0!hi0!hkb!ku1!k0!lic!jj4!im7!in3!hm4>5HCEIL$b>0@3$5$6@1$c^1@2$d@2$1@1$0#k0?3sp0+ogggg0@4$9^2@1$8@2$2@1$3?1h?1E@1$4$7@4$a@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$2@1$3?1h?1E?4FULL").
  Proof.
    intros HCEIL Hh'. npose (fs_geom_ceil HCEIL Hh') as (G1 & G2 & G3 & G4).
    apply RFSI_init; [exact G1 | exact G2 | exact G3 | exact G4 | exact fs_tls | apply hdr_zero; exact fs_hdr | exact fs_flags | exact fs_frames | exact fs_shadow].
  Qed.
End AT_MAIN.
(* [comment removed for export] *)
