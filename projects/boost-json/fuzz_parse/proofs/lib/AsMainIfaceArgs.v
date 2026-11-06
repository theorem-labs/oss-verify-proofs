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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsPrintfFirst AsDrvDefs AsMainPre.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import CatExec RefLayout ArgvEnv FileSim MuslStrlen.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan
  AsImages AsPlanImages AsHSTab AsStartupHSF AsMainVM AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsMainSyms.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool04andb79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAsMainIfaceArgs7AT_MAIN~~~~~~i46isSome69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsMainVM~~~~~~n78lin_ofxB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~rd2kn79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hg03lin69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainFacts~~~~~~hk88has_factrd5e_sp0rd6e_str003fst03nat37Corelib7Numbers7BinNumshqd1Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainCells~~~~~~hsb9all_holesrd3acsrd9atr_entryrd8e_argv1wrd6e_atrbrd6e_str1rd8kw_argv1hg05KWordhg02SAhg04expr79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~im74bctxim74mkbc04true37Corelib4Init5Logicis02eqi4aargs_checkhqd4Npos35stdpp9bitvectorbdefinitionsiuf2bv06length04list03nil37Corelib5Lists7ListDefji53nth3h5LinuxProcessSemanticsfLinuxProcessSem5Statejk37in_argvhk82vE46Stdlib6ZArith6BinInt1Zjo26of_natjo23mulis03andjk37in_envpjo23addjo22lejo23sub3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutjt1h1build_stack_bytesjk38in_hwcapjk36in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~kj13APH79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~kn72uEhg06lin_of79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~ksb4lden04prod04pair04conshg04EVar03sndiufbbv_unsignedjo23pow37Corelib4Init5Peanolkf2ltji56firstn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ln3ccat_argv_ptr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lrdh3total_arg_bytes_nat04Some06optionis02ex3h5LinuxProcessSemanticsfLinuxProcessSem3Runmi4h1entry_stack_imagejt1cstack_to_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mn62wajo22lthk83Xofhk8chole_granted69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainIface~~~~~~mt37pm_vmemkj15ASEGSlrd3rdniuf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsMainPre~~~~~~nj77astr_at3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsno1h0word_to_le_byteshg06edenotlkf2le69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~ntdfloaded_segments36Stdlib5Lists4Listoi59nth_errormi48valid_spmi49valid_brkmi4avalid_argvmi4avalid_envpmi4h0entry_stack_fits69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSF~~~~~~oof8HSF_asanjk35in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~ou36ASAN_H69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~pi85LIMITpi85SINV0pi85argH0kn75cs_ok" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : ltac2:(zQ "10!ok5@1$0?3sp0").
  Hypothesis Vbrk : ltac2:(zQ "20!ol1!nhc@2$0$1?4brk0").
  Hypothesis Vav : ltac2:(zQ "20!ole!jn1@1$0@1$1?3inp").
  Hypothesis Vev : ltac2:(zQ "20!omc!jr2@1$0@1$1?3inp").
  Hypothesis Vfit : ltac2:(zQ "30!ona!jn1!jr2@3$0?3sp0@1$1?3inp@1$2?3inp").
  Hypothesis Hh : ltac2:(zQ "50!ih6!mh0!mh6!it4!ose@3$3@1$2$0@1$4?1h@2$1$0?2ch").
  Hypothesis HC : ltac2:(zQ "c0!jn1!jr2!khb!ki7!kn0!ota!phe!nhc!pm3!pmc!pn5!pne@b$b$7$6$8@8$9$4?3sp0?5rdraw?4brk0@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@7$a$4?3sp0?5rdraw@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@1$5?3inp?1E?2ch?1R?4FULL?5model").
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
  #[local] Notation kp_b25 := (AsMainIface.kp_b25 h E) (only parsing).   (* [comment removed for export] *)
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
  #[local] Notation vr_b25 := (AsMainIface.vr_b25 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).   (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
  Definition args_check : ltac2:(zQ "10!h8$0") := ltac2:(zQ "h80!he!me!r2!vb!hk1!ho6!hp2!hpa!h8!hq3!hq8!hs6!ig9!ih6!ihc!ii8!ij3!ijc!ik5!il0!il9!ilf!iqa!ir2@1$c\1g$8\3cls$a\2ch$d=2bc$h6@1$h7@1$3^1@2$0@2$0@2$0@2$0@2$0@2$0@2$5@1$3^2@3$h3@2$h4$6+8N8$7@2$5@1$3^2@1$h2$f@2$5@1$3^2$e@2$1$4@2$2^1$6@2$1$4@2$2^1$7@2$1$4@2$2^1$h1@2$1$4@2$2^1@3$9$h5$b$h0").
  Lemma args_check_ok : ltac2:(zQ "40!h8!ira!it4!ita@3$2$0$3$1").
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma cs_v3 : ltac2:(zQ "b0!iu7!jgc!jh2!jha!ji0!it4!jjc!hs6!jn1!jnc!jpa@3$5$7@2$9?1EN3@1$a@2$2@1$1@1$0#8@4$6@1$3@1$1@1$0#8N0@1$8?3inp@1$4@1$1@1$0#8").
  Proof.
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 3%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. apply u_of_Z.
    npose Vav as (Hl & _ & Hs & _ & _). assert (Hin : In (nth 0 argv []) argv) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) Hs _ Hin) as L. cbv beta in L. lia.
  Qed.
  Lemma W_facts : ltac2:(zQ "h30!jh2!iu7!jnc!jq4!jpa!jgc!jha!jqb!jn1!jr2!jrd!js4!jsa!it4!hs6!kg5!khb!ki7!kn0@2$7@2$bZ@2$2?1EN4@2$7@3$d$e@2$3+8@2$2?1EN4@2$c@2$c@1$4@2$0@1$5@1$1#8@7$f$h2?3sp0@1$8?3inp@1$9?3inp@1$h1?3inp@1$h0?3inp?5rdraw+h0@2$a@2$a@2$3+8@1$4@2$0@1$6@1$5@1$1#8@1$8?3inp@2$3+8@1$4@2$0@1$6@1$5@1$1#8@1$9?3inp+r8@2$b@2$2?1EN4+kkls0").
  Proof.
    npose (AsanInit.W_range APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vav Vev) as (W1 & W2 & W3).
    destruct (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as [HE _]. unfold vE. rewrite (HE 4%nat) by (unfold NX0; lia).
    cbn [ev E0 vals0 nth]. rewrite u_of_Z by lia. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma no_wrap : ltac2:(zQ "d0!it4!h8!ira!hs6!me!r2!vb!krb!ilf!hk1!ks1!ir2!lh2>1e$8>0@3$0$1@2$4$9@2$5@1$b@1$6?2ch^1$2@3$0$3@2$7?1E^2@2$c?1E@1$a^2").
  Proof.
    intros e H. destruct (lin_ofxB (mkbc (kn ch)) e) as [l|] eqn:L; [|discriminate].
    rewrite lin_ofxB_eqf in L. pose proof (lin_ofx_sound _ _ _ _ KNF _ _ L) as S.
    unfold lin_ofx in L. destruct (lin_nowrapR (kn ch) e); [|discriminate]. injection L as <-. exact S.
  Qed.

  (* [comment removed for export] *)
  Lemma lin_e_sp0 : ltac2:(zQ "c0!hs6!ilf!lha!li0!li6!lic!jha!ji0!it4!hp2!hk1!ks1@3$8$a@1$b$9@4$3$0@1$6@2$2$0$1Z@3$4@2$2$0$1@4$3$0$1+ogg0@1$5N0@3$4@2$2$0$1@4$3$0$1+hgg0@1$5N6@3$4@2$2$0$1@4$3$0$1+h0@1$5Na@1$7@2$2$0$1").
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_str0 : ltac2:(zQ "c0!hs6!ilf!lha!li0!li6!lic!jha!ji0!it4!hpa!hk1!ks1@3$8$a@1$b$9@4$3$0@1$6@2$2$0$1+r8@3$4@2$2$0$1@4$3$0$1+ogg0@1$5N0@3$4@2$2$0$1@4$3$0$1+8@1$5N1@3$4@2$2$0$1@4$3$0$1+8@1$5N2@3$4@2$2$0$1@4$3$0$1+hgg0@1$5N6@3$4@2$2$0$1@4$3$0$1+h0@1$5Na@1$7@2$2$0$1").
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_str1 : ltac2:(zQ "c0!hs6!ilf!lha!li0!li6!lic!jha!ji0!it4!ijc!hk1!ks1@3$8$a@1$b$9@4$3$0@1$6@2$2$0$1+r9@3$4@2$2$0$1@4$3$0$1+ogg0@1$5N0@3$4@2$2$0$1@4$3$0$1+8@1$5N1@3$4@2$2$0$1@4$3$0$1+8@1$5N2@3$4@2$2$0$1@4$3$0$1+1@1$5N3@3$4@2$2$0$1@4$3$0$1+hgg0@1$5N6@3$4@2$2$0$1@4$3$0$1+h0@1$5Na@1$7@2$2$0$1").
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_atrb : ltac2:(zQ "f0!hs6!ilf!lha!li0!li6!lic!it4!ij3!hq3!jha!ji0!lj4!jqb!hk1!ks1@2$c@3$6$d@1$e@3$8$1$0$7@4$3$0@1$9@2$2$0$1Z@3$4@2$2$0$1@4$3$0$1+ogg0@1$5N0@3$4@2$2$0$1@4$3$0$1+8@1$5N1@3$4@2$2$0$1@4$3$0$1+8@1$5N2@3$4@2$2$0$1@4$3$0$1+8@1$5N4@3$4@2$2$0$1@4$3$0$1+hgg0@1$5N6@3$4@2$2$0$1@4$3$0$1+h0@1$5Na@1$a@2$2$0$1@3$6$0@3$b$1$0$7+r8").
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma arg_facts : ltac2:(zQ "i59!iu7!jrd!jgc!it4!jh2!jqb!hs6!jpa!jha!jn1!krb!jq4!lj9!h8!ira!jr2!ho6!vb!ij3!hp2!hpa!ilf!hq3!ji0!lj4!jjc!kg5!khb!ki7!kn0!ihc!ii8!ijc!ik5!il0!il9!jsa&@2$4@1$8@1$2@1$0#8@1$9?3inp&@1$7~0&@2$b+8~1&@2$1@2$c@1$0#k0?3sp0~2&@2$4@1$8@1$2@1$0#8@1$f?3inp&@1$7~4&@2$b+8~5&@2$1~3~6&@2$1~7+r8@2$5@3$3$d@2$h0@1$h1?2ch@3$i2@2$i3$h3+8N8$h4$e@2$5@3$3$d@2$h0@1$h1?2ch@1$i1$hf$e@2$5@3$3$d@2$h0@1$h1?2ch$he$e@2$5@3$3$6@2$a?1E$h3@2$c@1$0#k0?3sp0@2$5@3$3$6@2$a?1E$h4~8@2$5@3$3$6@2$a?1E$i0@2$1@2$1~8@1$7@2$4@1$2@1$0#8@4$h9@1$8@1$2@1$0#8N0@1$9?3inp@1$h7@1$2@1$0#8+1@3$3$6@2$1@2$a?1E@3$h6$h5$6$h2@3$h8$h5$6$h2@2$i4@2$1@2$c@1$0#k0?3sp0@1$7@2$4@1$2@1$0#8@7$ha$hd?3sp0@1$9?3inp@1$f?3inp@1$hc?3inp@1$hb?3inp?5rdraw+h0").
  Proof.
    pose proof args_check_ok as H0. unfold args_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply andb_prop in H as [H N4]. apply andb_prop in H as [H N3]. apply andb_prop in H as [H N2]. apply andb_prop in H as [H N1].
    apply andb_prop in H as [H F3]. apply andb_prop in H as [F1 F2].
    npose (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & SP & _ & _ & V1 & V2 & _).
    pose proof cs_v3 as V3. npose W_facts as (W1 & W2 & W3).
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
    rewrite (no_wrap _ N1), (no_wrap _ N2), (no_wrap _ N3), (no_wrap _ N4).
    pose proof lin_e_atrb as [LA SA]. rewrite lin_e_sp0, lin_e_str0, lin_e_str1, LA, SA.
    unfold lden. cbn [fst snd tden]. rewrite !uE_var. rewrite V1, V2, V3. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma lay : ltac2:(zQ "h17!iu7!jh2!js4!jpa!jgc!jqb!jha!jn1!jr2!jrd!lj9!kg5!khb!ki7!kn0!jq4!lk8&@2$1@1$6@1$4@1$0#8@1$7?3inp&@1$3~0&@2$1@1$6@1$4@1$0#8@1$8?3inp&@1$3~2&@7$b$e?3sp0@1$7?3inp@1$8?3inp@1$d?3inp@1$c?3inp?5rdraw&@2$1@1$4@1$0#8~4&@1$3~5@2$5@2$2@2$9@2$9@2$f+8~1@2$f+8~3+s8~6@2$5@2$2@2$9@2$a@1$0#k0?3sp0~6@2$h0+2+if@2$5@2$5@2$2+1~1@2$2~1+kg0@2$5@2$5@2$2Z~3@2$2~3+hg0@2$5@2$2+nvvvogggggg0@2$a@1$0#k0?3sp0@2$2@2$a@1$0#k0?3sp0+ogggggggggg0").
  Proof.
    pose proof (AsanInit.bsb_ge APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp)) as [G _].
    pose proof (AsanInit.usp_fit APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vfit) as UF.
    pose proof (AsanInit.len_av APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vav) as LA.
    pose proof (AsanInit.len_ev APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vev) as LE.
    pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2. repeat split; lia.
  Qed.
  Lemma u_ptr : ltac2:(zQ "h11!iu7!jha!jn1!jrd!jgc!jh2!jpa!jr2!jq4!lj9!hq8!it4!lm3!lm9!hs6!lqd!lv8&@2$5@1$1@1$4@1$0#8@1$2?3inp>1k$a>0@2$c^1~0@3$b$e@2$9@1$0#k0@4$f?3sp0@1$2?3inp@1$7?3inp^2@2$3@2$3@2$3@2$3@2$9@1$0#k0?3sp0@2$8+8@1$6~0@2$8+8@1$6@2$5@1$1@1$4@1$0#8@1$7?3inp+r8@1$6@1$h0@3$d@1$1@1$4@1$0#8^2@1$2?3inp").
  Proof.
    intros k Hk. pose proof Vsp as [V1 [V2 _]].
    rewrite (RefLayout.u_cat_argv_ptr APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vav Vev V1 V2 k Hk).
    unfold cat_struct_size. change auxv_size with 160%nat. lia.
  Qed.
  Lemma room : ltac2:(zQ "h30!iu7!jgc!jn1!jh2!jrd!jha!jr2!jpa!lj9!hq8!ji0!lm3!jjc!kg5!khb!ki7!kn0!lqd!js4>1k$9>0@2$b^1@2$3@1$5@1$1@1$0#8@1$2?3inp@2$h2@2$4@2$4@2$8@1$0#k0@4$h1?3sp0@1$2?3inp@1$6?3inp^2@1$7@2$3@1$1@1$0#8@4$c@1$5@1$1@1$0#8^2@1$2?3inp@1$a@1$1@1$0#8+h1@2$4@2$8@1$0#k0?3sp0@1$7@2$3@1$1@1$0#8@7$d$h0?3sp0@1$2?3inp@1$6?3inp@1$f?3inp@1$e?3inp?5rdraw").
  Proof.
    intros k Hk. pose proof Vsp as [V1 [V2 _]].
    exact (MuslStrlen.argv_ptr_room APH sp0 argv envp (in_uid inp) (in_hwcap inp) rdraw Vav Vev V1 V2 k Hk).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma stack_to_mem_some : ltac2:(zQ "h70!iu7!jgc!jn1!jr2!khb!ki7!kn0!lj9!mh0!jh2!mh6!jqb!it4!mhe!hs6!ml0!kg5!mm6!mr0!jrd!js4!mr6!jpa>1x$e>0@2$b@2$h4@2$7@1$0#k0?3sp0^1@2$h5^1@2$h3@2$7@1$0#k0?3sp0@1$h6@2$9@1$1@1$0#8@7$h0$6?3sp0@1$2?3inp@1$3?3inp@1$5?3inp@1$4?3inp?5rdraw@2$d@1$1@1$0#8\1b@1$1@1$0#8@3$c@1$a@1$1@1$0#8@3$h1?3sp0@7$f$6?3sp0@1$2?3inp@1$3?3inp@1$5?3inp@1$4?3inp?5rdraw@1$h2^3@2$8@1$1@1$0#8^1").
  Proof.
    intros x Hx. npose lay as (G & UF & LA & LE & VS). unfold stack_to_mem. rewrite !(wa_unsigned x) by lia.
    replace (sp0z <=? x) with true by (symmetry; apply Z.leb_le; lia).
    unfold entry_stack_image. rewrite length_app.
    destruct (Z.ltb_spec (x - sp0z) (Z.of_nat (length BSB + length (entry_slack sp0 BSB (ed_slack rdraw))))); [|exfalso; lia].
    destruct (nth_error _ (Z.to_nat (x - sp0z))) as [b|] eqn:Hn; [exists b; reflexivity|].
    apply nth_error_None in Hn. rewrite length_app in Hn. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma block_full : ltac2:(zQ "h80!iu7!jrd!jgc!jh2!jn1!jr2!jpa!jha!khb!ki7!kn0!mr0!jq4!lj9!mh6!jqb!it4!hs6!ml0!kg5!mm6!js4!mr6!jsa>1x$h1>0@2$f@2$h5@2$1@2$1@2$1@2$d@1$0#k0?3sp0@2$c+8@1$6@2$3@1$7@1$2@1$0#8@1$4?3inp@2$c+8@1$6@2$3@1$7@1$2@1$0#8@1$5?3inp+r8^1@2$h6^1@2$h7@2$1@2$d@1$0#k0?3sp0@1$6@2$3@1$2@1$0#8@7$h3$a?3sp0@1$4?3inp@1$5?3inp@1$9?3inp@1$8?3inp?5rdraw+h0@3$h0@1$e@1$2@1$0#8@1?4FULL@1$b^2@3$h4?3sp0@7$h2$a?3sp0@1$4?3inp@1$5?3inp@1$9?3inp@1$8?3inp?5rdraw@1$b^2").
  Proof.
    intros x Hx. npose lay as (G & UF & LA & LE & VS). npose W_facts as (W1 & W2 & W3).
    rewrite <- (wrap_above_sp APH sp0 argv envp (wa x) (in_uid inp) (in_hwcap inp) rdraw) by (rewrite wa_unsigned by lia; lia).
    apply (pmc_args _ _ _ _ _ _ MC). unfold argB0. rewrite wa_unsigned by lia.
    apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma atr_full : ltac2:(zQ "h64!iu7!jgc!jh2!kg5!jn1!jr2!khb!ki7!kn0!jrd!jpa!lj9!mh0!mh6!jqb!it4!mhe!hs6!mr0!js4!mr6!jsa&@7$3$8?3sp0@1$4?3inp@1$5?3inp@1$7?3inp@1$6?3inp?5rdraw&@2$2@1$1@1$0#8~0&@1$a~1&@2$9@2$b@1$0#k0?3sp0~2>1x$h1>0@2$e@2$h3@2$h5~3+h0^1@2$h4^1~3@2$h0@1$1@1$0#8\1b@1$1@1$0#8@3$f@1$d@1$1@1$0#8@1?4FULL@1$h2^3@2$c@1$1@1$0#8^1").
  Proof.
    intros x Hx. npose arg_facts as (_ & _ & F3 & _ & _ & _ & UA). npose lay as (G & UF & _).
    unfold has_fact in F3. apply existsb_exists in F3 as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. unfold atr_entry in KO. cbn [kentry_ok] in KO. ndestruct KO as (FL & LEN & BL).
    unfold elenZ in BL, LEN. fold (uE E (ELit 16)) in BL, LEN. rewrite (uE_lit' 16 ltac:(lia)) in BL, LEN.
    assert (ES : estart E (SA (fst e_atrb) (snd e_atrb)) = sp0z + Z.of_nat (length BSB) - 16).
    { unfold estart. cbn [a_base a_off]. fold (uE E (fst e_atrb)). exact UA. }
    specialize (BL (x - estart E (SA (fst e_atrb) (snd e_atrb))) ltac:(lia)).
    replace (estart E (SA (fst e_atrb) (snd e_atrb)) + (x - estart E (SA (fst e_atrb) (snd e_atrb)))) with x in BL by lia.
    eexists. apply Mr_some'. exact BL.
  Qed.

  (* [comment removed for export] *)
  Lemma upper_vm_some : ltac2:(zQ "ha0!iu7!jgc!jrd!lj9!jh2!jpa!jha!jn1!jr2!jq4!mh0!mh6!jqb!it4!mhe!hs6!kg5!khb!ki7!mrc!ms3!nh1!kn0!mr0!js4!mr6>1x$f>0@2$c@2$h8@2$2@2$2@2$2@2$3@1$0#k0?3sp0@2$9+8@1$5@2$4@1$6@1$1@1$0#8@1$7?3inp@2$9+8@1$5@2$4@1$6@1$1@1$0#8@1$8?3inp+r8^1@2$h9^1@2$2@2$3@1$0#k0?3sp0@1$5@2$4@1$1@1$0#8@7$h0$h6?3sp0@1$7?3inp@1$8?3inp@1$h2?3inp@1$h1?3inp?5rdraw@2$e@1$1@1$0#8\1b@1$1@1$0#8@3$d@1$b@1$1@1$0#8@5$h5@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$h3@1$h4?1h?1E?4FULL@1$h7^3@2$a@1$1@1$0#8^1").
  Proof.
    intros x Hx. npose lay as (G & UF & LA & LE & VS). pose proof pd_facts as PD.
    rewrite (vm_stack x ltac:(lia)).
    destruct (Z.lt_ge_cases x (sp0z + Z.of_nat (length BSB) - 16)) as [L|L].
    - rewrite (block_full x ltac:(lia)). apply stack_to_mem_some. lia.
    - apply atr_full. lia.
  Qed.

  Lemma rdn_some_of : ltac2:(zQ "h30!iu7!jgc!jha!mh6!js4!mh0!it4!mhe!hs6!jrd!jpa!hq8!jqb!nhc!mr0!ni5!mr6!lk8!nic>1m>1x@1$1@1$0#k0@1$3@1$1@1$0#8>1n$b>1a$8>0@2$4Z^1>0@2$4@2$9^2@1$a^3@2$h1+2+k0>0>1x$8>0@2$c@2$4^4^1@2$h0^1@2$9^4@1$a^5@2$7@1$1@1$0#8\1b@1$1@1$0#8@3$6@1$3@1$1@1$0#8@1^8@1$e^3@2$5@1$1@1$0#8^1@2$7@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8@3$6@1$3@1$2@1$1@1$0#8@4$f$d^7@2$h2@1$0#k0^5^6@2$5@1$2@1$1@1$0#8^1").
  Proof.
    intros m n. induction n as [|n IH]; intros a Ha Hn H; [exists []; reflexivity|].
    cbn [rdn]. destruct (H a ltac:(lia)) as [b Hb]. unfold wa in Hb. rewrite Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros x Hx; apply H; lia)) as [bs Hbs].
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    - rewrite Hbs. exists (b :: bs). reflexivity.
    - apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. change (bv_unsigned (1%bv : word)) with 1. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wa_word : ltac2:(zQ "50!iu7!jgc!it4!mr0!lj9>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@1$3@2$4@1$0#k0^1^1").
  Proof. intros x. unfold wa. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

  Lemma arg_string : ltac2:(zQ "h00!iu7!jn1!jgc!lj9!jha!jh2!hq8!ji0!lm3!jjc!jr2!nn6!mrc!ms3!nh1!lqd>1k$6>0@2$8^1@2$5@1$4@1$2@1$0#8@1$1?3inp@4$b@4$e@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$c@1$d?1h?1E?4FULL?3sp0@2$3@1$0#k0@4$f?3sp0@1$1?3inp@1$a?3inp^2@4$9@1$4@1$2@1$0#8^2@1$1?3inp@1$7@1$2@1$0#8").
  Proof.
    intros k Hk. npose lay as (G & UF & LA & LE & VS). pose proof pd_facts as PD. pose proof Vsp as [VS1 [VS2 _]].
    pose proof (u_ptr k Hk) as UP. pose proof (room k Hk) as RM.
    pose proof (total_arg_bytes_firstn_le k argv) as TF.
    pose proof (RefLayout.lay_bsb_nw APH sp0 rdraw argv envp (in_uid inp) (in_hwcap inp) Vav Vev VS2) as NW.
    unfold astr_at. change Asan.M.loaded_segments with ASEGS.
    set (p := bv_unsigned (cat_argv_ptr sp0 argv envp k)) in *.
    split; [lia|]. split; [lia|]. split.
    { npose Vav as (_ & _ & _ & Hn & _). apply (proj1 (Forall_forall _ _) Hn). apply nth_In. exact Hk. }
    split.
    - (* [comment removed for export] *)
      rewrite <- (read_argv_cstr_k APH ASEGS sp0 argv envp k (in_uid inp) (in_hwcap inp) rdraw Hk NW).
      replace (Z_to_bv 64 p) with (cat_argv_ptr sp0 argv envp k) by (subst p; symmetry; apply wa_word).
      apply rdn_ext; [fold p; lia|]. intros x Hx. fold p in Hx. rewrite <- (wa_word x).
      rewrite (vm_stack (bv_unsigned x) ltac:(pose proof (u64_range x); lia)). apply block_full. lia.
    - (* [comment removed for export] *)
      apply (rdn_some_of VM 8 (p + Z.of_nat (length (nth k argv [])))); [lia | lia |]. intros x Hx. apply upper_vm_some. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma slot_main : ltac2:(zQ "he0!iu7!jgc!jha!it4!jrd!lj9!js4!mh0!h8!jh2!mh6!ira!hs6!nr8!jn1!mrc!ho6!ms3!nh1!nhc!hp2!vb!il0!il9!nsd!ilf!ni5!jq4!jpa!nic>3off$c>1v$h9>1w@1$1@1$0#k0>0@3$3$8@2$h0@1$h5?2ch@3$h6@2$h7$h4^3N8^2$b>0@2$6Z^4>0@2$6@2$4^5+8@2$4@2$hb+8@1$hc@2$9@1$2@1$1@1$0#8@1$e?3inp+h0>0@3$3@1$1@1$0#k0@2$h8?1E^5^4@3$3@1$a@1$2@1$1@1$0#8@4$ha$h3@4$h2@2$5@1$0#k0?3sp0@2$5@1$0#k0?4brk0@2$f@1$h1?1h?1E?4FULL@2$hd@1$0#k0@2$4@2$5@1$0#k0?3sp0^7N8@2$7@1$2@1$1@1$0#8@2$dN8^5").
  Proof.
    intros off v w HF Ho1 Ho2 Hv. npose lay as (G & UF & LA & LE & VS). pose proof pd_facts as PD.
    npose arg_facts as (_ & _ & _ & USP & _).
    unfold has_fact in HF. apply existsb_exists in HF as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. cbn [kentry_ok] in KO. ndestruct KO as (_ & FL & RD).
    assert (Ha : adenot E (SA e_sp0 off) = Z_to_bv 64 (sp0z + off)).
    { apply bv_eq. rewrite (flat_u E _ _ FL). unfold estart. cbn [a_base a_off]. fold (uE E e_sp0). rewrite USP, u_of_Z; [reflexivity | lia]. }
    rewrite Ha, Hv in RD.
    assert (RF : rdn ASEGS FULL (Z_to_bv 64 (sp0z + off)) 8 = Some (word_to_le_bytes 8 w)).
    { apply (rdn_Mr_full _ _ _ RD). intros i Hi. rewrite u_of_Z by lia. apply hid_stack. lia. }
    rewrite <- RF. apply rdn_ext; [rewrite u_of_Z by lia; lia|]. intros x Hx. rewrite u_of_Z in Hx by lia.
    rewrite <- (wa_word x). apply vm_stack. lia.
  Qed.

  Lemma arg_ptr0 : ltac2:(zQ "h20!iu7!lj9!jha!jgc!mh0!mh6!it4!nr8!jn1!jr2!mrc!ms3!nh1!nhc!lqd!ni5!jrd!nic@3$6@1$5@1$2@1$3@1$0#8@4$f$d@4$c@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$a@1$b?1h?1E?4FULL@2$h1@1$0#k0@2$h0@2$1@1$0#k0?3sp0+8N8@2$4@1$2@1$3@1$0#8@2$7N8@4$e?3sp0@1$8?3inp@1$9?3inpN0").
  Proof.
    npose lay as (G & UF & LA & LE & VS). npose arg_facts as (F1 & _ & _ & _ & US0 & _).
    apply (slot_main 8 e_str0 _ F1); [lia | lia |].
    apply bv_eq. change (bv_unsigned (edenot E e_str0)) with (uE E e_str0). rewrite US0, (u_ptr 0 ltac:(lia)). replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity. lia.
  Qed.

  Lemma arg_ptr1 : ltac2:(zQ "h40!iu7!jha!jgc!lj9!jn1!mh0!jh2!mh6!it4!nt7!nr8!jr2!mrc!ms3!nh1!nhc!lqd!ni5!jrd!nic>0@2$9N2@2$6@1$1@1$2@1$0#8@1$4?3inp@3$8@1$7@1$1@1$2@1$0#8@4$h1$f@4$e@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$c@1$d?1h?1E?4FULL@2$h3@1$0#k0@2$h2@2$3@1$0#k0?3sp0+h0N8@2$5@1$1@1$2@1$0#8@2$aN8@4$h0?3sp0@1$4?3inp@1$b?3inpN1").
  Proof.
    intros H2. npose lay as (G & UF & LA & LE & VS). npose arg_facts as (_ & F2 & _ & _ & US0 & US1 & _).
    npose (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V1 & _).
    unfold kw_argv1 in F2. apply (slot_main 16 e_argv1w _ F2); [lia | lia |].
    apply bv_eq. rewrite (u_ptr 1 ltac:(lia)).
    unfold e_argv1w. cbn [edenot]. rewrite u_mul64, u_sltu64, u_lit64a.
    change (bv_unsigned (ev E V_ARGC)) with (vE E 1). rewrite V1. change (1 mod 2 ^ 64) with 1.
    replace (1 <? argc) with true by (symmetry; apply Z.ltb_lt; lia).
    change (bv_unsigned (edenot E e_str1)) with (uE E e_str1). rewrite US1, Z.mul_1_l.
    assert (T1 : forall l : list (list byte), (2 <= length l)%nat -> total_arg_bytes_nat (firstn 1 l) = (length (nth 0 l []) + 1)%nat).
    { intros [|x0 l0] Hl; cbn [length] in Hl; [lia|]. cbv [firstn fold_right total_arg_bytes_nat nth]. lia. }
    rewrite (T1 _ H2).
    npose Vav as (_ & _ & Hs & _ & _). pose proof (proj1 (Forall_forall _ _) Hs _ (@nth_In _ 0 argv [] ltac:(cbn [length]; lia))) as L0. cbv beta in L0.
    rewrite Z.mod_small; lia.
  Qed.

  Lemma wa_word0 : ltac2:(zQ "50!iu7!jgc!it4!nic!lj9>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3@1$0#k0@2$4@1$0#k0^1^1").
  Proof. intros x. exact (wa_word x). Qed.

  (* [comment removed for export] *)
  Theorem pre_args : ltac2:(zQ "h91!iu7!jha!jgc!lj9!mh0!mh6!it4!hs6!mrc!ms3!nh1!jrd!nic!hq8!jqb!mhe!lm3!nr8!jn1!nn6!ni5!oh2!oj8!jq4!jpa&@4$a@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$8@1$9?1h?1E?4FULL>1i$d>1s@1$1@1$2@1$0#8>0@2$h0^2N2>0@3$6@1$5@1$1@1$2@1$0#8@3$h6@1$1@1$2@1$0#8@1$h2?3inp^3@2$4@1$1@1$2@1$0#8^2@2$f$7\1p$7@2$e@3$6@1$5@1$1@1$2@1$0#8@4$h4$h5~0@2$c@1$0#k0@2$b@2$b@2$3@1$0#k0?3sp0+8@2$h7+8@1$h8^5N8@2$4@1$1@1$2@1$0#8@2$h1N8@2$c@1$0#k0^1@4$h3~0?3sp0^1^4").
  Proof.
    intros i s Hi Hs. change Asan.M.loaded_segments with ASEGS.
    assert (Hk : (i < length argv)%nat) by exact (nth_error_lt _ _ _ Hs).
    assert (Hn : nth i argv [] = s) by exact (nth_error_nth _ _ [] Hs).
    exists (bv_unsigned (cat_argv_ptr sp0 argv envp i)). split; [| rewrite <- Hn; apply arg_string; exact Hk].
    rewrite wa_word0.
    destruct i as [|[|i]]; [ | | lia].
    - replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (sp0z + 8) by lia. apply arg_ptr0.
    - replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 1) with (sp0z + 16) by lia. apply arg_ptr1. lia.
  Qed.
End AT_MAIN.
(* [comment removed for export] *)
