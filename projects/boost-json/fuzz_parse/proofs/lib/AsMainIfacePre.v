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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsStack0 AsPrintfFirst AsDrvDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan
  AsImages AsPlanImages AsHSTab AsStartupHSF AsMainVM AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AsMainSyms.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJA Require Import BJRep.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14Nonek16option37Corelib4Init5Logicm92eqhfbbv_unsigned69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainFacts~~~~~~p03Xofp0chole_granted69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainIface~~~~~~u37pm_vmem01Zk14boolk14truem93and69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsMainCells~~~~~~hk29img_check46Stdlib6ZArith6BinInt1Zhod2lehod2lthf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsDrvDefs~~~~~~hrbbarelro_none79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ig95asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ikd7mem_invk14list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~ip98list_eqbhod3eqb79OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsMainIfacePre7AT_MAIN~~~~~~iua9bytes_eqbk14prodk13natk13orbiuaeovl_cell_checkiuaerom_cell_check79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~jn77cell_okjn78cells_okiuaacell_check36Stdlib5Lists4Listjud7forallbhrbaadrv_cellshrb8astdout0hrb8adrv_ax1hk22cxhk25world79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~kk04exprhk24csymk13fstk13sndhk2ball_holes_whk29csym_baseip93acsip9akentry_eqbip92knkk05KWordkk02SAkk06kentryjud7existsbhod3addhk26cx_valhod6of_natk14Some37Corelib4Init5Peanolha2lt3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticslj4h0word_to_le_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsaAsMainSyms~~~~~~lo08pm_shorthk28world_oku36vrangeiuadkword_check_w69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsPlanImages~~~~~~lv25ASEGSkk06edenot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~mk43rdnhod3powhrb9atid_celllo06ps_tidm92exhrb7acanary79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mr44cellk14consk13nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~ng56AERRNOmr42C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~nl28rw_cellskk03lin79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~nq04bctxk15falsekk05saddrk14andb3h5LinuxProcessSemantics5Riscv5Instrog35aluopog35mulop69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsMainVM~~~~~~oj97le_linBhod3leboj98lin_ofaBhod3ltboj98lin_ofxBk14pairkk04EVarhk29all_holesiua4LSTKiua4kwr1nq04mkbciua6LSHLENiua6LSHSTKiua6kzero1iua9stk_checkiua9shz_check79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~ph14ldenhod3sub69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAsMainLazy~~~~~~pm75SHOFFlo09page_downhod3divikd2wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ps73stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~qga2b879OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsStack0~~~~~~qkb6stack069OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~qp38HeapCeilqp35hceilm91Imk44getrhf2BVhf4BvWfk16length3h5LinuxProcessSemanticsfLinuxProcessSem5Staterg47in_argvng53ATPrg47FdEntryrg49FdChannelrg45m_fds3h5LinuxProcessSemanticsfLinuxProcessSem2Fsrm52Fsrg45in_fsrg44m_fs3h5LinuxProcessSemanticsfLinuxProcessSem3Runrq78valid_sprq79valid_brkrq7avalid_argvrq7avalid_envprg47in_envprq7h0entry_stack_fits69OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsStartupHSF~~~~~~si88HSF_asanrg48in_hwcaprg46in_uidlv23APH69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsImages~~~~~~sp06ASAN_H69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~st55LIMITst55SINV0st55argH079OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~tib5cs_ok" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : ltac2:(zQ "10!rt3@1$0?3sp0").
  Hypothesis Vbrk : ltac2:(zQ "20!rtf!mj1@2$0$1?4brk0").
  Hypothesis Vav : ltac2:(zQ "20!ruc!rj2@1$0@1$1?3inp").
  Hypothesis Vev : ltac2:(zQ "20!rva!sg8@1$0@1$1?3inp").
  Hypothesis Vfit : ltac2:(zQ "30!sh3!rj2!sg8@3$0?3sp0@1$1?3inp@1$2?3inp").
  Hypothesis Hh : ltac2:(zQ "50!kr9!lh3!m0!nd!sm7@3$3@1$2$0@1$4?1h@2$1$0?2ch").
  Hypothesis HC : ltac2:(zQ "c0!rj2!sg8!sn3!snf!so9!rp6!ssb!mj1!th0!th9!ti2!tmf@b$b$7$6$8@8$9$4?3sp0?5rdraw?4brk0@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@7$a$4?3sp0?5rdraw@1$0?3inp@1$1?3inp@1$3?3inp@1$2?3inp@1$5?3inp?1E?2ch?1R?4FULL?5model").
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
  #[local] Notation CXV a := (cx_val sp0z brk0z X a).
  #[local] Notation MR := (Mr ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model FULL).
  #[local] Notation HID := (hid ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model).
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma vm_none_of : ltac2:(zQ "90!h9!jc!l9!m0!nd!o2!se!t4!hi1>1a@1$1@1$0#k0>0@3$4@1$3@1$1@1$0#8@1?4FULL^1@1$2@1$1@1$0#8@3$4@1$3@1$1@1$0#8@5$8@2$5@1$0#k0?3sp0@2$5@1$0#k0?4brk0@2$6@1$7?1h?1E?4FULL^2@1$2@1$1@1$0#8").
  Proof. intros a H. unfold pm_vmem, restrict_mem, restrict_mem_by. destruct (hiddenb _ _ a); [reflexivity | exact H]. Qed.

  Lemma img_none_main : ltac2:(zQ "h10!h9!hib!nd!jc!o2!l9!hie!m0!hj5!hjc!ho0!se!t4!hi1!hq5!hqb!hr1>2lo$1>2hi$1>0@3$2$6@2$a^2^1$8>1i$1>0@2$9@2$e^4^1@2$f^1^3@3$2@1$7@1$3@1$0#8@5$d@2$4@1$0#k0?3sp0@2$4@1$0#k0?4brk0@2$b@1$c?1h?1E?4FULL@2$h0@1$0#k0^2@1$5@1$3@1$0#8").
  Proof. intros lo hi H i Hi. apply vm_none_of. exact (pmc_img _ _ _ _ _ _ MC lo hi H i Hi). Qed.

  Lemma pre_relro : ltac2:(zQ "60!h9!o2!hva!se!t4!hi1@1$2@4$5@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$3@1$4?1h?1E?4FULL").
  Proof. exact (img_none_main 0x1ad000 0x1b7000 ltac:(vm_cast_no_check (@eq_refl bool true))). Qed.
  Lemma pre_glb : aglb_none VM.
  Proof. split; [exact (img_none_main 0x1b9ff0 0x1b9ff8 ltac:(vm_cast_no_check (@eq_refl bool true))) | exact (img_none_main 0x1ba0e0 0x1bcb80 ltac:(vm_cast_no_check (@eq_refl bool true)))]. Qed.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pre_inv : ltac2:(zQ "70!h9!o2!ik4!se!t4!hi1!io7@2$6$2@4$5@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$3@1$4?1h?1E?4FULL").
  Proof.
    intros a b H. unfold ro_addr. rewrite asegs_ASEGS.
    destruct (find_segment ASEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|reflexivity].
    apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asan_segs_eq in Hin.
    destruct (seg_writable seg) eqn:SW; [reflexivity|]. exfalso.
    assert (HR : 0x10000 <= bv_unsigned a < 0x1ad000).
    { destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hb, Ht, SW; try discriminate SW; lia. }
    pose proof (img_none_main 0x10000 0x1ad000 ltac:(vm_cast_no_check (@eq_refl bool true)) (bv_unsigned a) HR) as N.
    replace (Z_to_bv 64 (bv_unsigned a)) with a in N by (apply bv_eq; rewrite Z_to_bv_unsigned; symmetry; apply bv_wrap_small; apply bv_unsigned_in_range). congruence.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bytes_eqb : ltac2:(zQ "40!ip2!h9!jc!hie>2xs@1$0@1$2@1$1#8>2ys@1$0@1$2@1$1#8$3") := ltac2:(zQ "60!h9!jc!ip2!o2!it7!iu3\2xs@1$2@1$1@1$0#8\2ys@1$2@1$1@1$0#8@4$4@1$1@1$0#8\1x@1$1@1$0#8\1y@1$1@1$0#8@2$5@2$3@1$0#8^2@2$3@1$0#8^1^2^1").
  Lemma bytes_eqb_eq : ltac2:(zQ "70!ip2!h9!jc!nd!hie!hj5!jj3>2xs@1$0@1$2@1$1#8>2ys@1$0@1$2@1$1#8>0@3$3$4@2$6^2^1$5@3$3@1$0@1$2@1$1#8^3^2").
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
    Z.leb 0x1ad000 a && Z.leb (a + Z.of_nat w) 0x716000 && bytes_check (CAbs, a) (map bv_unsigned (word_to_le_bytes w (Z_to_bv 64 v))).
  Definition cell_check : ltac2:(zQ "40!jk0!hib!hie!jk7>1c@2$0@2$0$1$3$1$2") := ltac2:(zQ "60!jk0!hib!jk7!jkd!jl3!jm5\1c@2$0@2$0$1$2$1@2$3@1$5^1@1$4^1").

  Lemma rom_cell_main : ltac2:(zQ "d0!jk0!h9!hib!o2!hie!jk7!hj5!nd!js8!se!t4!hi1!jm5>1c@2$0@2$0$2$5$2>0@3$7$4@1$c^1$6@2$8@4$b@2$3@1$1#k0?3sp0@2$3@1$1#k0?4brk0@2$9@1$a?1h?1E?4FULL^2").
  Proof.
    intros [[a w] v] H. unfold rom_cell_check in H. apply andb_prop in H as [HI HR].
    pose proof HI as HI'. unfold img_check in HI'. apply andb_prop in HI' as [HI' _]. apply andb_prop in HI' as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
    destruct (rdn ASEGS (fun _ => None) (Z_to_bv 64 a) w) as [bs|] eqn:RD; [|discriminate]. apply bytes_eqb_eq in HR. subst bs.
    unfold cell_ok. rewrite <- RD. apply rdn_ext; [rewrite u_of_Z by lia; lia|].
    intros x Hx. rewrite u_of_Z in Hx by lia. replace x with (Z_to_bv 64 (bv_unsigned x)) by (apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range). apply (img_none_main _ _ HI). lia.
  Qed.
  Lemma ovl_cell_main : ltac2:(zQ "d0!jk0!h9!hib!o2!hie!jk7!hj5!nd!js8!se!t4!hi1!jl3>1c@2$0@2$0$2$5$2>0@3$7$4@1$c^1$6@2$8@4$b@2$3@1$1#k0?3sp0@2$3@1$1#k0?4brk0@2$9@1$a?1h?1E?4FULL^2").
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
  Lemma cells_main : ltac2:(zQ "f0!jk0!hib!jk7!h9!o2!hie!ip2!hj5!nd!jt3!se!t4!hi1!jtf!kg0>2cs@1$6@2$0@2$0$1$2$1>0@3$8$5@3$e@2$0@2$0$1$2$1$d^1$7@2$9@4$c@2$4@1$3#k0?3sp0@2$4@1$3#k0?4brk0@2$a@1$b?1h?1E?4FULL^2").
  Proof.
    intros cs H. unfold cells_ok. apply Forall_forall. intros c Hc. pose proof (proj1 (forallb_forall _ _) H c Hc) as H1.
    unfold cell_check in H1. apply orb_prop in H1 as [H1|H1]; [apply rom_cell_main | apply ovl_cell_main]; exact H1.
  Qed.

  Lemma pre_cells : ltac2:(zQ "70!h9!o2!kgb!jt3!se!t4!hi1@2$3@4$6@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$4@1$5?1h?1E?4FULL$2").
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  Lemma pre_out : ltac2:(zQ "70!h9!o2!kh9!jt3!se!t4!hi1@2$3@4$6@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$4@1$5?1h?1E?4FULL$2").
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  (* [comment removed for export] *)
  Lemma pre_ax1 : ltac2:(zQ "70!h9!o2!ki5!jt3!se!t4!hi1@2$3@4$6@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$4@1$5?1h?1E?4FULL$2").
  Proof. apply cells_main. vm_cast_no_check (@eq_refl bool true). Qed.
  (* [comment removed for export] *)
  Lemma pre_bj : bj_statics VM.
  Proof.
    unfold bj_statics. cbv delta [BJ_INSTANCE BJ_DR_VTBL BJ_DR_D1 BJ_DR_D0 BJ_DO_ALLOC BJ_DO_DEALLOC BJ_DO_ISEQ BJ_ARR_EMPTY BJ_OBJ_EMPTY BJ_ERRCAT BJ_ERRCAT_VTBL BJ_ERRCAT_ID BJ_FAILED_FN].
    change Asan.M.loaded_segments with ASEGS.
    split; [apply img_cells_main; vm_cast_no_check (@eq_refl bool true)|].
    split; [apply img_cells_main; vm_cast_no_check (@eq_refl bool true)|].
    split; [apply img_cells_main; vm_cast_no_check (@eq_refl bool true)|].
    split; [exists (wz 0); apply img_cells_main; vm_cast_no_check (@eq_refl bool true)|].
    split; apply img_cells_main; vm_cast_no_check (@eq_refl bool true).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kword_check_w : ltac2:(zQ "50!hie!jk7!kj1!kj7!ko1>1w$3>1a$2>2wd$1>2ve$4$0") := ltac2:(zQ "h40!hib!ko1!hie!jk7!jk0!ko9!kp1!kp7!kpd!kqc!kj1!kj7!kr9!ks0!kse!kt4!ktd!ku3!kud!kv8\1w$b\1a$a\2wd$3\2ve$1@2$8^4\1g$2\3cls$3\2ch$cM4\1p@2$4$1$0$2@3$9^3^2@3$6$5$0^6\1b$1\1k$0@3$h2$h1@1$d@3$f@2$h0^2@2$h3^1@3$7$5$0^8^7^6@1$e^3").
  Lemma kword_main : ltac2:(zQ "hf1!h9!o2!t4!se!kvf!ip2!nd!kv8!hq5!lg9!jc!lh3!hie!jk7!m0!hj5!lie!lmb!ls0!kj1!kj7!lsc!hi1!lt8!lu1!mj1!mja!ko1!mnf!mo6!hr1&@4$4@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$3@1$2?1h?1E^8>1w$h4>1a$h3>2wd$d>2ve$hb>0@3$6$c@4$h8^4^3^2^1$f>0@3$h5^5@1$h2@2$1@1$0#k0?3sp0@1$2?1h>0@2$h0N0^4>0@2$8Z@4$4@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$3@1$2?1h?1E^6>0@2$8@2$7@4$4@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$3@1$2?1h?1E^7@1$9^6@2$hd+2+k0>0@8$h7?3sp0?4brk0?3inp?1h?1E?4FULL~0@2$7~0@1$9^7@3$6@1$e@1$5@1$a@1$0#8@4$hc$h9@4$h6@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$3@1$2?1h?1E?4FULL@2$he@1$0#k0@4$4@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$3@1$2?1h?1E^9^8@2$b@1$5@1$a@1$0#8@2$h1^8@2$ha?1E^7").
  Proof.
    intros w [s off] wd ve H Hw Hwd0 H0 H1 VR. apply (all_holes_w_here w) in H; [|exact (hole_sel_here w Hw)].
    cbn [fst snd] in H.
    ndestruct (csym_den s) as (D1 & D2 & D3).
    destruct (csym_base g cls s) as [b k] eqn:CB. cbn [fst snd] in D1, D2, D3.
    apply existsb_exists in H as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. cbn [kentry_ok] in KO. ndestruct KO as (Hwd & FL & RD).
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

  Lemma pre_tid : ltac2:(zQ "70!h9!se!t4!o2!mod!mpa!hi1@2$4@4$6@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$1@1$2?1h?1E?4FULL@1$5@2$1@1$2?1h?1E").
  Proof.
    npose (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & VTID & _).
    split; [|unfold Xof; cbn [ps_tid]; lia].
    pose proof (kword_main w_all (CAbs, 0x6f4330) 4 (EVar K_TID) ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)) as W.
    revert W. pmc_simpl. rewrite Z.add_0_l. intros W. change Asan.M.loaded_segments with ASEGS.
    rewrite (W ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)). do 2 f_equal. apply bv_eq.
    unfold Xof. cbn [ps_tid]. change (bv_unsigned (edenot E (EVar K_TID))) with (vE E K_TID). rewrite u_of_Z; [reflexivity | lia].
  Qed.

  Lemma pre_can : ltac2:(zQ "80!h9!hib!o2!mq4!mq9!se!t4!hi1@2$3$1\3can$1@2$4@4$7@2$2@1$0#k0?3sp0@2$2@1$0#k0?4brk0@2$5@1$6?1h?1E?4FULL^1").
  Proof.
    exists (bv_unsigned (edenot E (EVar 61))). split; [|apply u64_range].
    pose proof (kword_main w_all (CAbs, 0x714418) 8 (EVar 61) ltac:(vm_cast_no_check (@eq_refl bool true)) (world_ok_all _ _) ltac:(lia)) as W.
    revert W. pmc_simpl. rewrite Z.add_0_l. intros W. change Asan.M.loaded_segments with ASEGS.
    rewrite (W ltac:(lia) ltac:(lia) ltac:(apply vr_img; lia)). do 2 f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_errno : ltac2:(zQ "e0!h9!mv0!jc!o2!mv8!mvf!mq4!ik4!nk2!se!t4!hi1!nkc!nod@2$6@1$2@1$0#k0\1e@1$2@1$0#k0@4$d$7@4$b@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$9@1$a?1h?1E?4FULL$8@3$4$1@1$c^1@1$5$1").
  Proof.
    exists (wz 0). unfold AERRNO, ATP.
    pose proof (rom_cell_main (0x6f4334, 4%nat, 0) ltac:(vm_cast_no_check (@eq_refl bool true))) as RD. unfold cell_ok in RD.
    change Asan.M.loaded_segments with ASEGS in RD.
    apply rw_cells_img; [cbn; tauto | lia | csz; lia |].
    apply bytes_at_of_nth; [lia | csz; lia |]. intros i Hi. rewrite asegs_ASEGS.
    replace (cells_bytes [C4 (wz 0)]) with (word_to_le_bytes 4 (Z_to_bv 64 0)) in Hi |- * by reflexivity.
    exact (rdn_mrd ASEGS (word_to_le_bytes 4 (Z_to_bv 64 0)) VM 0x6f4334 RD ltac:(lia) ltac:(cbn; lia) i Hi).
  Qed.

  (* [comment removed for export] *)
  Lemma pre_latch : ltac2:(zQ "h00!h9!jc!ip2!o2!lh3!mv8!mvf!m0!nd!mq4!se!t4!hi1!mj1!mnf!hr1@2$9@1$1@1$0#8\2ib@1$1@1$0#8@3$8@1$7@1$2@1$1@1$0#8@4$e$d@4$c@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$a@1$b?1h?1E?4FULL@2$f@1$0#k0+mviop0N1@2$4@1$2@1$1@1$0#8@3$5@1$1@1$0#8^1@1$6@1$1@1$0#8").
  Proof.
    cbn [rdn]. destruct (VM (Z_to_bv 64 7284880)) as [b|] eqn:HV; [exists b; reflexivity|].
    destruct (img_rw_rom 0x6f2890 ltac:(lia)) as [b Hb]. unfold wa in Hb. rewrite Hb. exists b. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kwr1 : ltac2:(zQ "50!hie!hib!ku3!np9!nu3>2bc$4>2qa$3>1n$1>1K$2$0") := ltac2:(zQ "h20!ko1!nub!hib!nv3!jk7!hie!nvc!ku3!np9!m0!oi7!oj0!on4!onf!oo6!nu3!op2!mo6\2bc$f\2qa$8\1n$2\1K$7M7\1K$7$5^1\1a$3\1w$4\1v$0$1\1a$3\2n0$0$1\1a$3\2n0$0\1k$4$1\2lo$2\2hi$2$1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\2za$3\2n0$0M0\2n0$0$5^1\2zn$2M9\1x@1$9$8$5@2$e^7^3\2l0$8@2$6@2$6@2$6@2$6@3$c^8^1^7@3$c^8^7^1@2$d^6^2@2$dZ^2@2$h0^2@2$h1+2+je$1\2n1$4$1\2op$a\1a$0\1b$0$1\2op$a\1a$0\1b$0$1\2op$b\1a$0\1b$0$1\2op$b\1a$0\1b$0$1\2sx$5\2lo$4\2n1$4\1e$0$1\2sx$5\1k$4\1i$2\2n1$4$1\2a1$3\2n1$0\2a2$3\2n2$0$1\1a$3\2n0$0\1c$2$1\1a$3\2n0$0$1").
  (* [comment removed for export] *)
  Definition kzero1 : ltac2:(zQ "40!np9!hie!ku3!nu3>2bc$3>2qa$0>2qn$0>1K$2$1") := ltac2:(zQ "e0!nub!ko1!nv3!hib!np9!m0!hie!on4!ku3!nvc!jk7!oo6!op9!nu3\2bc$d\2qa$4\2qn$4\1K$8M8\1K$8$6^1\1a$2\1w$a\1v$1$0\2za$2\2zn$1M5\1x@1$5$4$6@2$b^6^2\2l0$4M5\1x@1$5$4$6@2$c^7^2\2ln$4@2$9@2$9@3$7^8^2^7@3$7^8^7^2@3$7^8^6^1$0$0\1a$2\1n$1\1k$a$0\2lo$3\2hi$3$0\1e$1\1m$3$0\1e$1\2lo$3\2hi$3$0\1a$2\1n$1$0\2a1$2\2n1$1\2a2$2\2n2$1$0\1a$2\1n$1\1c$3$0\1a$2\1n$1$0").
  (* [comment removed for export] *)
  Definition LSTK : ltac2:(zQ "10!np9$0") := ltac2:(zQ "80!hib!ko1!jk0!oq5!mv8!oqc!ip2!mvf@4$3$0@1$6@2$2$0$1-ogggg0@3$4@2$2$0$1@4$3$0$1+ogg0@1$5N0@3$4@2$2$0$1@4$3$0$1+hgg0@1$5N6@3$4@2$2$0$1@4$3$0$1+h0@1$5Na@1$7@2$2$0$1").
  Definition LSHSTK : ltac2:(zQ "10!np9$0") := ltac2:(zQ "80!hib!ko1!jk0!oq5!mv8!oqc!ip2!mvf@4$3$0@1$6@2$2$0$1+nvuvogg0@3$4@2$2$0$1@4$3$0$1+hgg0@1$5N0@3$4@2$2$0$1@4$3$0$1+ig0@1$5N6@1$7@2$2$0$1").
  Definition LSHLEN : ltac2:(zQ "10!np9$0") := ltac2:(zQ "80!hib!ko1!jk0!oq5!mv8!oqc!ip2!mvf@4$3$0@1$6@2$2$0$1+hggggghgggg0@3$4@2$2$0$1@4$3$0$1-hgg0@1$5N0@3$4@2$2$0$1@4$3$0$1-ig0@1$5N6@1$7@2$2$0$1").
  Definition stk_check : ltac2:(zQ "10!hie$0") := ltac2:(zQ "a0!kse!hie!jk7!or4!os1!os9!kr9!ku3!ot1!kud@1$3\1g$1\3cls$2\2ch$6@3$9$7@3$5@1$8@1$0^1$4+ogggg0@1$0^1").
  Definition shz_check : ltac2:(zQ "10!hie$0") := ltac2:(zQ "b0!kse!hie!jk7!or4!ot9!ou3!oud!kr9!ku3!ot1!kud@1$3\1g$1\3cls$2\2ch$7@3$a$8@3$6@1$9@1$0^1$5$4@1$0^1").
  Lemma stk_check_ok : ltac2:(zQ "40!hie!hj5!nd!ov7@3$2$0$3$1").  Proof. vm_compute. reflexivity. Qed.
  Lemma shz_check_ok : ltac2:(zQ "40!hie!hj5!nd!pg4@3$2$0$3$1").  Proof. vm_compute. reflexivity. Qed.

  Lemma lden_LSTK : ltac2:(zQ "70!nd!h9!hib!os1!pl8!pm0!o2@3$0$2@2$4?1E$3@2$5@2$6@1$1#k0?3sp0+ogggg0").
  Proof.
    npose (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & SP & _).
    unfold LSTK, lden. cbn [fst snd tden]. rewrite !uE_var. lia.
  Qed.
  Lemma lden_LSH : ltac2:(zQ "e0!pl8!kv8!nd!hib!ou3!pq4!hjc!h9!pqd!ot9!pra!mo6!pm0!o2@2$6@3$2$3@2$0?1E$4@2$1$5@2$a@2$c@1$8@2$d@1$7#k0?3sp0+ogggg0+8@3$2$3@2$1@2$0?1E$4@2$0?1E$9@2$1$5@2$b+2+ic").
  Proof.
    npose (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PGD & _).
    unfold LSHSTK, LSHLEN, lden, SHOFF. cbn [fst snd tden]. rewrite !uE_var. rewrite <- PGD. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_full : ltac2:(zQ "d0!h9!jc!o2!lh3!m0!hjc!nd!mq4!hib!ps1!hq5!hqb!pm0>1z$8>0@2$5@2$a@2$c@2$2@1$0#k0?3sp0+ogggg0^1@2$b^1@2$2@1$0#k0?3sp0@2$7@1$1@1$0#8\1b@1$1@1$0#8@3$6@1$4@1$1@1$0#8@1?4FULL@1$9^3@2$3@1$1@1$0#8^1").
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
  Lemma pre_stk : ltac2:(zQ "a0!h9!o2!hq5!hib!ik4!se!t4!hi1!qg3!pm0>2lo$3>0@2$2@2$9@2$1@1$0#k0?3sp0+ogggg0^1>0@2$2^2@2$1@1$0#k0?3sp0@4$8$4@4$7@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$5@1$6?1h?1E?4FULL^3@2$1@1$0#k0?3sp0").
  Proof.
    intros lo H1 H2. pose proof Vsp as [V1 [V2 _]]. unfold sp_window_lo, sp_window_hi in V1, V2.
    pose proof pd_facts as PD.
    apply stk_of_some; [lia | lia |]. intros a Ha.
    destruct (stack_full a ltac:(lia)) as [b Hb]. exists b. rewrite <- Hb. apply vm_stack. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_shadow_zero : ltac2:(zQ "h50!h9!o2!pq4!kv8!jc!lh3!m0!hjc!nd!hib!pqd!se!t4!hi1!ps1!qk5!pra!hq5!hqb!mo6!pm0>1z$9>0@2$7@2$h1@2$3$2@2$h0@2$h4@1$a@2$1@1$0#k0?3sp0+ogggg0+8^1@2$h2^1@2$3$2@2$h3+2+ic@3$8@1$6@1$4@1$0#8@5$d@2$1@1$0#k0?3sp0@2$1@1$0#k0?4brk0@2$b@1$c?1h?1E?4FULL@1$e^2@2$5@1$4@1$0#8@1$fZ").
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
    - unfold VISZ, VISZ0. apply in_or_app. left. do 16 right. left. reflexivity.   (* [comment removed for export] *)
    - replace (page_down sp0z - 8388608 + (140737496743936 - page_down sp0z)) with (17592186044416 * 8) by lia. apply Z_mod_mult.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_sh0 : ltac2:(zQ "h00!h9!hib!o2!hq5!hjc!pm0!nd!mq4!pqd!qo9!se!t4!hi1!qse!qta!mo6>5HCEIL$d>0@3$6$1@1$e^1@2$5@2$2@1$0#k0?3sp0+ogggg0>2lo$1>0@2$4@2$3@2$5@1$8@2$2@1$0#k0?3sp0+ogggg0^1@2$3^1@2$f+2+if@2$7$1\3shi$1@2$4@4$9^5@4$c@2$2@1$0#k0?3sp0@2$2@1$0#k0?4brk0@2$a@1$b?1h?1E?4FULL^3^1@2$3+ogggggggggg0^1").
  Proof.
    intros HCEIL Hh' lo Hlo. npose pd_facts as (PD1 & PD2 & PD3). exists (2 ^ 47). split; [|lia].
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
  Lemma pre_regs : ltac2:(zQ "h10!h9!jc!qu3!nd!qu7!quf!qv4!hr1!hjc!o2!qvb!ip2!rj2!rjd!kv8!lg9!pm0@2$8@3$3@1$1@1$0#k0@2$4?1R@3$5@1$0#5+1Kv$2@2$6@1$0#5+1@2$7@1$0#k0+hpjti4@2$8@3$3@1$1@1$0#k0@2$4?1R@3$5@1$0#5+2Kv$2@2$6@1$0#5+2@2$7@1$0#k0@2$h0@2$9@1$0#k0?3sp0+j0@2$8@3$3@1$1@1$0#k0@2$4?1R@3$5@1$0#5+4Kv$2@2$6@1$0#5+4@2$7@1$0#k0$d@2$8@3$3@1$1@1$0#k0@2$4?1R@3$5@1$0#5+aKv$2@2$6@1$0#5+a@2$7@1$0#k0@1$f@2$a@1$b@1$1@1$0#8@1$c?3inp@3$3@1$1@1$0#k0@2$4?1R@3$5@1$0#5+bKv$2@2$6@1$0#5+b@2$7@1$0#k0@2$e@2$9@1$0#k0?3sp0+8").
  Proof.
    pose proof (pm_regs _ _ _ _ _ PMo) as RG. cbv zeta in RG. cbn [cfg_ms cfg_of mkst ms_regs] in RG.
    ndestruct RG as (R1 & R2 & R3 & R4 & R8 & R9 & R10 & R11 & _). unfold ATP.
    repeat split; try assumption; rewrite R2; f_equal; lia.
  Qed.
  Lemma pre_fds : ltac2:(zQ "c0!h9!rk4!jc!hr1!jk0!mv8!oq5!rkf!ip2!mvf!nd!rlc@3$a@1$8@2$4@1$2@1$0#k0$1@1$b?5model@3$5@2$4@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$3@1$0#k0Z@1$7@2$3@1$0#k0Z@3$5@2$4@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$3@1$0#k0+1@1$7@2$3@1$0#k0+1@3$5@2$4@1$2@1$0#k0$1@4$6@1$2@1$0#k0$1@2$3@1$0#k0+2@1$7@2$3@1$0#k0+2@1$9@2$4@1$2@1$0#k0$1").
  Proof. exact (pm_fds _ _ _ _ _ PMo). Qed.
  Lemma pre_fs : ltac2:(zQ "40!nd!rp0!rp6!rpf@3$0$1@1$3?5model@1$2?3inp").
  Proof. exact (pm_fs _ _ _ _ _ PMo). Qed.
End AT_MAIN.
(* [comment removed for export] *)
