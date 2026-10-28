(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsanAllocCons. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import LazyRestrict LazySR.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AllocWf AllocRep AllocRepX AsDepotInv AG_Malloc2 FakeStackRep
  AS_InstWF AS_InstMainDefs AS_InstDefs AS_InstMainRep AS_InstMainK AS_InstMainVis.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsStartupHSF. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceDepot AsMainIfaceAlloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import PerfLia.
Import ListNotations. Import AX2. Import AP. Import APS.
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
  #[local] Notation rw_cells_out := (AsMainIfaceAlloc.rw_cells_out sp0 brk0 inp) (only parsing).
  #[local] Notation obj_word_out := (AsMainIfaceAlloc.obj_word_out sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_bytes_out := (AsMainIfaceAlloc.obj_bytes_out sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zero_cells := (AsMainIfaceAlloc.zero_cells sp0 brk0 rdraw h E FULL) (only parsing).
  #[local] Notation zero_stk := (AsMainIfaceAlloc.zero_stk sp0 brk0 h E FULL) (only parsing).
  #[local] Notation zero_u8arr := (AsMainIfaceAlloc.zero_u8arr sp0 brk0 rdraw h E FULL) (only parsing).
  #[local] Notation img_stk := (AsMainIfaceAlloc.img_stk sp0 brk0 h E FULL) (only parsing).
  #[local] Notation img_wr := (AsMainIfaceAlloc.img_wr sp0 brk0 h E FULL) (only parsing).
  #[local] Notation al_ceil := (AsMainIfaceAlloc.al_ceil sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_top := (AsMainIfaceAlloc.al_top sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation geo := (AsMainIfaceAlloc.geo sp0) (only parsing).
  #[local] Notation al_T := (AsMainIfaceAlloc.al_T sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_CTX := (AsMainIfaceAlloc.al_CTX sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_R6 := (AsMainIfaceAlloc.al_R6 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_PA := (AsMainIfaceAlloc.al_PA sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_FSB := (AsMainIfaceAlloc.al_FSB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_D := (AsMainIfaceAlloc.al_D sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_B11 := (AsMainIfaceAlloc.al_B11 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_SB := (AsMainIfaceAlloc.al_SB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zdisj := AsMainIfaceAlloc.zdisj (only parsing).
  #[local] Notation al_apart := (AsMainIfaceAlloc.al_apart sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_stack := (AsMainIfaceAlloc.al_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_lits := AsMainIfaceAlloc.al_lits (only parsing).
  #[local] Notation al_lits_check := AsMainIfaceAlloc.al_lits_check (only parsing).
  #[local] Notation al_lits_main := (AsMainIfaceAlloc.al_lits_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation al_lit := (AsMainIfaceAlloc.al_lit sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_releasems := (AsMainIfaceAlloc.in_releasems sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_premapped := (AsMainIfaceAlloc.in_premapped sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_ptrsize := (AsMainIfaceAlloc.in_ptrsize sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_nreserved := (AsMainIfaceAlloc.in_nreserved sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_secmutex := (AsMainIfaceAlloc.in_secmutex sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_quar := (AsMainIfaceAlloc.in_quar sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_qmutex := (AsMainIfaceAlloc.in_qmutex sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_gq := (AsMainIfaceAlloc.in_gq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_fbmutex := (AsMainIfaceAlloc.in_fbmutex sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_maxuser := (AsMainIfaceAlloc.in_maxuser sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_fill := (AsMainIfaceAlloc.fl_fill sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_psg := (AsMainIfaceAlloc.fl_psg sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_pp := (AsMainIfaceAlloc.fl_pp sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_ndtm := (AsMainIfaceAlloc.fl_ndtm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_fastuw := (AsMainIfaceAlloc.fl_fastuw sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_csmt := (AsMainIfaceAlloc.fl_csmt sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_mmaplim := (AsMainIfaceAlloc.fl_mmaplim sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_decorate := (AsMainIfaceAlloc.fl_decorate sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_c219 := (AsMainIfaceAlloc.fl_c219 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_c244 := (AsMainIfaceAlloc.fl_c244 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_shbase := (AsMainIfaceAlloc.fl_shbase sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_highend := (AsMainIfaceAlloc.fl_highend sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_canpoison := (AsMainIfaceAlloc.fl_canpoison sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_inited := (AsMainIfaceAlloc.fl_inited sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_ctxsize := (AsMainIfaceAlloc.fl_ctxsize sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_tsdinit := (AsMainIfaceAlloc.fl_tsdinit sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_allocfl := (AsMainIfaceAlloc.fl_allocfl sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_iainit := (AsMainIfaceAlloc.fl_iainit sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_hooks := (AsMainIfaceAlloc.fl_hooks sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_dying := (AsMainIfaceAlloc.fl_dying sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_realms := (AsMainIfaceAlloc.fl_realms sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_got := (AsMainIfaceAlloc.fl_got sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_pagesz := (AsMainIfaceAlloc.fl_pagesz sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_secname := (AsMainIfaceAlloc.fl_secname sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_primname := (AsMainIfaceAlloc.fl_primname sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_tlsslot := (AsMainIfaceAlloc.fl_tlsslot sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_lsandis := (AsMainIfaceAlloc.fl_lsandis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_got2 := (AsMainIfaceAlloc.fl_got2 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fx_libcpgsz := (AsMainIfaceAlloc.fx_libcpgsz sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fx_gotssp := (AsMainIfaceAlloc.fx_gotssp sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fx_canary := (AsMainIfaceAlloc.fx_canary sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation in_spacebeg := (AsMainIfaceAlloc.in_spacebeg sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_regioninfo := (AsMainIfaceAlloc.in_regioninfo sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_chunks := (AsMainIfaceAlloc.in_chunks sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_ptrbase := (AsMainIfaceAlloc.in_ptrbase sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation in_hdr := (AsMainIfaceAlloc.in_hdr sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fl_tsd := (AsMainIfaceAlloc.fl_tsd sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation ia_zero_scan := AsMainIfaceAlloc.ia_zero_scan (only parsing).
  #[local] Notation seg_rom_bss_ia := (AsMainIfaceAlloc.seg_rom_bss_ia sp0 brk0 inp) (only parsing).
  #[local] Notation ia_pristine := (AsMainIfaceAlloc.ia_pristine sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation ia_main := (AsMainIfaceAlloc.ia_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_ctx := (AsMainIfaceAlloc.th_ctx sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_stack := (AsMainIfaceAlloc.th_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_w24 := (AsMainIfaceAlloc.th_w24 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_b40 := (AsMainIfaceAlloc.th_b40 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_zero41 := (AsMainIfaceAlloc.th_zero41 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_tls := (AsMainIfaceAlloc.th_tls sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_dtv := (AsMainIfaceAlloc.th_dtv sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_fs := (AsMainIfaceAlloc.th_fs sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_zero80 := (AsMainIfaceAlloc.th_zero80 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_unw := (AsMainIfaceAlloc.th_unw sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_zero3169 := (AsMainIfaceAlloc.th_zero3169 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_tq := (AsMainIfaceAlloc.th_tq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_cells0 := (AsMainIfaceAlloc.th_cells0 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_stk80 := (AsMainIfaceAlloc.th_stk80 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_u8z80 := (AsMainIfaceAlloc.th_u8z80 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_cells0_hi := (AsMainIfaceAlloc.th_cells0_hi sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_stk3169 := (AsMainIfaceAlloc.th_stk3169 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation th_stk41 := (AsMainIfaceAlloc.th_stk41 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation cx_tid := (AsMainIfaceAlloc.cx_tid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation cx_thr := (AsMainIfaceAlloc.cx_thr sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation ri_zero := (AsMainIfaceAlloc.ri_zero sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation ri_cells0 := (AsMainIfaceAlloc.ri_cells0 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation ri_stk := (AsMainIfaceAlloc.ri_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation ri_u8z := (AsMainIfaceAlloc.ri_u8z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation pa_empty := (AsMainIfaceAlloc.pa_empty sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation athr_cells_main := (AsMainIfaceAlloc.athr_cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation ak_limit := (AsMainIfaceAlloc.ak_limit sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_top := (AsMainIfaceAlloc.ak_top sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_eager := (AsMainIfaceAlloc.ak_eager sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_reserved := (AsMainIfaceAlloc.ak_reserved sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_res_list := AsMainIfaceAlloc.ak_res_list (only parsing).
  #[local] Notation ak_maps := (AsMainIfaceAlloc.ak_maps sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_noacc := (AsMainIfaceAlloc.ak_noacc sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_lazy := (AsMainIfaceAlloc.ak_lazy sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak1 := (AsMainIfaceAlloc.ak1 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak1_lo := (AsMainIfaceAlloc.ak1_lo sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak9 := (AsMainIfaceAlloc.ak9 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zz_in := (AsMainIfaceAlloc.zz_in sp0 brk0) (only parsing).
  #[local] Notation zz_cases := (AsMainIfaceAlloc.zz_cases sp0 brk0) (only parsing).
  #[local] Notation zz_out := (AsMainIfaceAlloc.zz_out sp0 brk0) (only parsing).
  #[local] Notation zz_contains := AsMainIfaceAlloc.zz_contains (only parsing).
  #[local] Notation ak_maps_in := (AsMainIfaceAlloc.ak_maps_in sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_maps_contains := (AsMainIfaceAlloc.ak_maps_contains sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_maps_exact := (AsMainIfaceAlloc.ak_maps_exact sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_zr_in := (AsMainIfaceAlloc.ak_zr_in sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_lazy_in := (AsMainIfaceAlloc.ak_lazy_in sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_S_in := (AsMainIfaceAlloc.ak_S_in sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_noacc_cases := (AsMainIfaceAlloc.ak_noacc_cases sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation al_AE := (AsMainIfaceAlloc.al_AE sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_T := (AsMainIfaceAlloc.ak3_T sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_CTX := (AsMainIfaceAlloc.ak3_CTX sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_space := (AsMainIfaceAlloc.ak3_space sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_SB := (AsMainIfaceAlloc.ak3_SB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_PA := (AsMainIfaceAlloc.ak3_PA sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_FSB := (AsMainIfaceAlloc.ak3_FSB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_D := (AsMainIfaceAlloc.ak3_D sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak8a := (AsMainIfaceAlloc.ak8a sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak4_space := (AsMainIfaceAlloc.ak4_space sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak4_SB := (AsMainIfaceAlloc.ak4_SB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak4_PA := (AsMainIfaceAlloc.ak4_PA sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak4_hish := (AsMainIfaceAlloc.ak4_hish sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak4_losh := (AsMainIfaceAlloc.ak4_losh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak5_space := (AsMainIfaceAlloc.ak5_space sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak5_PA := (AsMainIfaceAlloc.ak5_PA sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak5_hish := (AsMainIfaceAlloc.ak5_hish sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak8c := (AsMainIfaceAlloc.ak8c sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_sh_ceil := (AsMainIfaceAlloc.ak_sh_ceil sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak3_hish := (AsMainIfaceAlloc.ak3_hish sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak4_hish_ceil := (AsMainIfaceAlloc.ak4_hish_ceil sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak5_hish_ceil := (AsMainIfaceAlloc.ak5_hish_ceil sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak8a_sh := (AsMainIfaceAlloc.ak8a_sh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak8b_sh := (AsMainIfaceAlloc.ak8b_sh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak8c_sh := (AsMainIfaceAlloc.ak8c_sh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ak_budget := (AsMainIfaceAlloc.ak_budget sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
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
  #[local] Notation kp_apart_ne := (AsMainIface.kp_apart_ne sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_facts := (AsMainIface.kp_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b06 := (AsMainIface.kp_b06 h E) (only parsing).
  #[local] Notation kp_b08 := (AsMainIface.kp_b08 h E) (only parsing).
  #[local] Notation kp_b22 := (AsMainIface.kp_b22 h E) (only parsing).
  #[local] Notation G_cases := (AsMainIface.G_cases sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b09 := (AsMainIface.kp_b09 h E) (only parsing).
  #[local] Notation kp_b10 := (AsMainIface.kp_b10 h E) (only parsing).
  #[local] Notation kp_b16 := (AsMainIface.kp_b16 h E) (only parsing).
  #[local] Notation kp_b21 := (AsMainIface.kp_b21 h E) (only parsing).
  #[local] Notation vr_b12 := (AsMainIface.vr_b12 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_word_main := (AsMainIface.img_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation pd_facts := (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  Variable HCEIL : HeapCeil.
  Hypothesis Hceil : hceil = sp0z - 8388608.
  Variables (env : list Z) (ts : bool) (AL0 : Z).
  #[local] Notation st0 := (cert_st0 X env ts).
  #[local] Notation s0 := (cert_s0 sp0z brk0z X env ts AL0).
  #[local] Notation d0 := (depot0 sp0z X).
  Variable p : iparams.
  Hypothesis Pfsb : ip_fsb p = ps_b16 X.
  Hypothesis PD : ip_D p = ps_b12 X.
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].

  (* [comment removed for export] *)
  Lemma arheap_main : ARHEAP s0 (lbp []) VM.
  Proof.
    split; [exact (AS_InstMainRep.arep_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC HCEIL Hceil env ts AL0)|].
    cbn [lbp map]. split; [constructor|]. intros b. unfold alb. cbn [a_st cert_s0]. unfold cert_st0. rewrite chunk_list_init. cbn. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma flagsx_main : flagsx_rep VM.
  Proof.
    unfold flagsx_rep, ALIBCPGSZ, AGOT_SSP, ASSPGUARD, ACFLAGS.
    split; [exact fx_libcpgsz|]. split; [exact fx_gotssp|]. split; [exact fx_canary|]. split; [exact fl_c219|].
    exists (b8 1). exact fl_c244.
  Qed.

  (* [comment removed for export] *)
  Lemma depot_main_s0 : DEPOT asegs d0 VM.
  Proof. exact (AsMainIfaceDepot.depot_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC). Qed.

  Lemma depot_placed_main : depot_placed s0 d0.
  Proof.
    pose proof (al_ceil HCEIL Hceil) as AC. pose proof al_SB as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (kp_facts _ _ kp_b21) as F21. pose proof (kp_facts _ _ kp_b22) as F22. cbn [fst snd] in F21, F22.
    pose proof (kp_apart_ne 4 10 _ _ ltac:(lia) kp_b09 kp_b21) as A1. pose proof (kp_apart_ne 4 11 _ _ ltac:(lia) kp_b09 kp_b22) as A2.
    pose proof (kp_apart_ne 2 10 _ _ ltac:(lia) kp_b06 kp_b21) as A3. pose proof (kp_apart_ne 2 11 _ _ ltac:(lia) kp_b06 kp_b22) as A4.
    pose proof (kp_apart_ne 5 10 _ _ ltac:(lia) kp_b10 kp_b21) as A5. pose proof (kp_apart_ne 5 11 _ _ ltac:(lia) kp_b10 kp_b22) as A6.
    pose proof (kp_apart_ne 3 10 _ _ ltac:(lia) kp_b08 kp_b21) as A7. pose proof (kp_apart_ne 3 11 _ _ ltac:(lia) kp_b08 kp_b22) as A8.
    cbn [fst snd] in A1, A2, A3, A4, A5, A6, A7, A8.
    unfold depot_placed, disj, a_sb, a_pa. cbn [a_st a_thr a_ctx cert_s0 cert_st0 as_space_beg as_ptr_array as_sec init_state init_state_q d_nb d_sb depot0].
    unfold kPageSize, kSpaceSize, kPtrArrayReserve. rewrite AC. unfold aapp, aapp_lo, aapp_hi, ASegs.AIMG_TOP, AsShadow.ALOWSH_LO, AsShadow.AHI_LO.
    repeat match goal with |- _ /\ _ => split end; try (intros sc Hin; destruct Hin); try (first [clear - F21 F22 A1 A2 S2 S3 S4 S5 A3 A4 A5 A6 A7 A8 AC; tlia | tlia]).   (* [comment removed for export] *)
  Qed.

  (* [comment removed for export] *)
  Lemma depot_tr_main : depot_tr p d0.
  Proof.
    unfold depot_tr. cbn [d_ids d_frames d_K d_hash depot0 idseq Z.to_nat Pos.to_nat seq map Pos.iter_op Nat.add].
    split; [lia|]. split; [intros id Hid; lia|]. split; [constructor; [intros []| constructor]|].
    unfold pm_nframes. destruct (pm_short sp0z); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma athr_main : ATHR p VM.
  Proof.
    pose proof (al_ceil HCEIL Hceil) as AC. pose proof al_D as (D1 & D2 & D3 & D4 & D5). cbn [fst snd] in D1, D2, D3, D4, D5.
    pose proof pd_facts as (PD1 & PD2 & PD3).
    unfold ATHR. rewrite PD. unfold kPageSize.
    split. { pose proof (img_word_main (ATP + 24) (CB12, 0) ltac:(vm_compute; reflexivity)) as W. revert W. pmc_simpl. rewrite Z.add_0_r. intros W. apply W; unfold ATP; lia. }
    split. { pose proof (obj_word_out (CB12, 24) (CAbs, ATP) _ _ ltac:(vm_compute; reflexivity) vr_b12) as W. revert W. pmc_simpl. rewrite Z.add_0_l. intros W. apply W; unfold ATP; lia. }
    split; [lia|]. split; [lia|]. split; [rewrite AC; lia|].
    apply akobj_intro_sep; [lia | rewrite AC; lia | unfold ASegs.AIMG_LO, ASegs.AIMG_TOP; lia | unfold AsShadow.ALOWSH_LO, AsShadow.AHI_LO; lia].
  Qed.

  (* [comment removed for export] *)
  Theorem rheap_main : IRHEAP p (IST s0 d0) [] VM.
  Proof.
    pose proof (AS_InstMainVis.awin_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC env ts AL0) as AWV.
    pose proof al_apart as AP. unfold zdisj in AP.
    destruct AP as (_ & _ & _ & A4 & _ & _ & _ & _ & _ & _ & A11 & _ & _ & _ & A15).
    pose proof (kp_apart_ne 8 10 _ _ ltac:(lia) kp_b16 kp_b21) as B1. pose proof (kp_apart_ne 8 11 _ _ ltac:(lia) kp_b16 kp_b22) as B2. cbn [fst snd] in B1, B2.
    unfold IRHEAP. cbn [i_s i_d]. unfold ILIVE_CNT_MAX, disj. cbn [a_fsb cert_s0 d_nb d_sb depot0 length Z.of_nat].
    split; [exact arheap_main|]. split; [constructor|]. split; [unfold ILIVE_CNT_MAX, AsDriverLaws.ADRV_CNT; cbn; lia|].
    split; [exact AWV|]. split; [exact flagsx_main|].
    split; [exact depot_main_s0|]. split; [exact depot_placed_main|]. split; [exact depot_tr_main|].
    unfold AFS_SIZE, kPageSize. rewrite Pfsb, PD.
    pose proof al_FSB as (GF1 & _). cbn [fst snd] in GF1.
    split; [lia|]. split; [lia|]. split; [reflexivity|]. split; [exact GF1|]. split; [lia|]. split; [exact athr_main|].
    split; [exists (wz 0xbe23c8), (wz 0xbe24b4); cbn [a_thr cert_s0]; exact th_tls|].
    split; [exact (AS_InstMainK.ashadow_main sp0 brk0 h E env ts AL0)|].
    pose proof (kp_apart_ne 2 7 _ _ ltac:(lia) kp_b06 (AsMainIface.kp_b12 h E)) as AD. cbn [fst snd] in AD. pose proof al_SB as (S1 & S2 & S3 & S4 & S5 & S6).
    cbn [a_sb a_st cert_s0 cert_st0 as_space_beg as_sec init_state init_state_q]. unfold kSpaceSize.
    (* [comment removed for export] *)
    pose proof (kp_apart_ne 4 7 _ _ ltac:(lia) (AsMainIface.kp_b09 h E) (AsMainIface.kp_b12 h E)) as AD9. pose proof (kp_apart_ne 3 7 _ _ ltac:(lia) (AsMainIface.kp_b08 h E) (AsMainIface.kp_b12 h E)) as AD8.
    pose proof (kp_apart_ne 10 7 _ _ ltac:(lia) (AsMainIface.kp_b21 h E) (AsMainIface.kp_b12 h E)) as AD21. pose proof (kp_apart_ne 11 7 _ _ ltac:(lia) (AsMainIface.kp_b22 h E) (AsMainIface.kp_b12 h E)) as AD22.
    cbn [fst snd] in AD9, AD8, AD21, AD22.
    unfold IDAPART. rewrite ?PD. cbn [a_sb a_thr a_pa a_st cert_s0 cert_st0 as_space_beg as_ptr_array as_sec init_state init_state_q d_nb d_sb depot0].
    unfold kSpaceSize, kPtrArrayReserve, kPageSize, disj.
    split; [repeat split; (first [clear - A4 A11 A15 B1 B2 GF1 AD S1 S2 S3 S4 S5 AD9 AD21 AD22 AD8; lia | lia])|]. split; [intros sc Hsc; destruct Hsc|].
    (* [comment removed for export] *)
    cbn [a_st cert_s0]. unfold cert_st0. split; [apply AsanAllocCons.PINV_init| apply AsanAllocCons.INITQ_init; reflexivity].   (* [comment removed for export] *)
  Qed.
End AT_MAIN.
