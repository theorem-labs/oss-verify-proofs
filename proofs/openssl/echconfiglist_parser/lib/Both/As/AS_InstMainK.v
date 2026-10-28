(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel LazyRestrict LazyLedger LazySR BackingAlgebra.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AllocWf AllocRep AllocRepX FakeStackRep AS_InstWF AS_InstMainDefs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsStartupHSF AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceFS AsMainIfaceAlloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
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
  #[local] Notation pd_facts := (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  Variable HCEIL : HeapCeil.
  Hypothesis Hceil : hceil = sp0z - 8388608.
  Variables (env : list Z) (ts : bool) (AL0 : Z).
  #[local] Notation st0 := (cert_st0 X env ts).
  #[local] Notation s0 := (cert_s0 sp0z brk0z X env ts AL0).
  #[local] Notation VMM := (m_vmmaps model).

  (* [comment removed for export] *)
  Lemma vis_main : restrict (zz2ww (PM_LAZY sp0z X)) (zz2ww (PM_S sp0z brk0z X)) (mkst R (Z_to_bv 64 A_MAIN) FULL (seg_rom ASEGS))
                   = mkst R (Z_to_bv 64 A_MAIN) VM (seg_rom asegs).
  Proof. rewrite asegs_ASEGS. reflexivity. Qed.
  Lemma vis_main_s0 : restrict (a_L s0) (a_S s0) (mkst R (Z_to_bv 64 A_MAIN) FULL (seg_rom ASEGS)) = mkst R (Z_to_bv 64 A_MAIN) VM (seg_rom asegs).
  Proof. exact vis_main. Qed.

  (* [comment removed for export] *)
  Lemma rfs_main : RFSI (ps_b16 X) [] VM.
  Proof. exact (AsMainIfaceFS.fs_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC HCEIL Hceil). Qed.
  Lemma rfs_main_s0 : RFSI (a_fsb s0) [] VM.
  Proof. exact rfs_main. Qed.

  (* [comment removed for export] *)
  Lemma s0_k : a_sb s0 = pm_space_beg X /\ a_pa s0 = ps_b08 X /\ a_thr s0 = ps_b09 X /\ a_ctx s0 = ps_b10 X /\ a_fsb s0 = ps_b16 X
               /\ a_Zr s0 = zz2ww (PM_ZR sp0z X) /\ a_L s0 = zz2ww (PM_LAZY sp0z X) /\ a_S s0 = zz2ww (PM_S sp0z brk0z X)
               /\ as_sec st0 = [] /\ (forall c, RB s0 c = pm_space_beg X + Z.shiftl c 32) /\ as_maps st0 =
                  [ mkMap (ps_b06 X) 0x2000011000 MkPrimaryReservation PROT_NONE true
                  ; mkMap (pm_space_beg X + kSpaceSize) kPageSize MkRegionInfo PROT_RW false
                  ; mkMap (ps_b08 X) kPtrArrayReserve MkPtrArrayReservation PROT_NONE true ].
  Proof. unfold a_sb, a_pa, RB, region_beg, cert_s0, cert_st0. cbn. unfold kRegionSizeLog. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ak6a : forall x : word, in_rangesb x (vm_noaccess VMM) = true -> in_rangesb x (vm_maps VMM) = true.
  Proof.
    intros x Hx. rewrite ak_maps. rewrite ak_noacc in Hx.
    rewrite (in_rangesb_zz _ x zz_ok_maps). rewrite (in_rangesb_zz _ x zz_ok_noacc) in Hx.
    rewrite <- (AsMainLazy.in_ivs_zz sp0 brk0 _ _ zz_ok_maps). rewrite <- (AsMainLazy.in_ivs_zz sp0 brk0 _ _ zz_ok_noacc) in Hx.
    rewrite <- ak_maps. rewrite <- ak_noacc in Hx. exact (co_nasub _ _ _ _ _ _ _ _ _ _ _ HC (bv_unsigned x) Hx).
  Qed.
  (* [comment removed for export] *)
  Lemma ak_nooverlap : nooverlap (vm_maps VMM).
  Proof.
    pose proof (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) as SE. induction SE as [|p l HF SE IH]; [exact I|].
    apply nooverlap_cons_intro; [| exact IH]. intros e' He'. pose proof (proj1 (Forall_forall _ _) HF e' He') as D.
    unfold iv_disjoint in D. unfold hi, lo. lia.
  Qed.
  Lemma ak_nowrap : entries_nowrap (vm_maps VMM) /\ entries_nowrap (vm_noaccess VMM).
  Proof.
    pose proof (co_wf _ _ _ _ _ _ _ _ _ _ _ HC) as (W1 & W2 & _). split; intros e He; unfold entry_nowrap, hi;
      [pose proof (W1 e He) as W | pose proof (W2 e He) as W]; unfold iv_wf, BackingAlgebra.B, BackingAlgebra.S in W; exact W.
  Qed.

  Theorem akernel_main : akernel s0 model.
  Proof.
    pose proof s0_k as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
    pose proof (al_ceil HCEIL Hceil) as AC. pose proof al_SB as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof al_CTX as (GC1 & GC2 & GC3 & GC4 & GC5). cbn [fst snd] in GC1, GC2, GC3, GC4, GC5.
    unfold akernel. cbv zeta. rewrite E1, E2, E3, E4, E5, E6, E7, E9. unfold kPageSize, kSpaceSize, kPtrArrayReserve, kRegionSize, kNumClasses, AFS_SIZE.
    split; [exact ak1|].
    split; [split; [exact ak_limit | exact (proj1 (al_top HCEIL Hceil))]|].
    split. { intros x [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
      - apply ak3_T. lia.
      - apply ak3_CTX. lia.
      - apply ak3_SB. lia.
      - apply ak3_PA. lia.
      - apply ak3_FSB. lia.
      - apply ak3_hish. exact Hx. }
    split. { intros a n c Hc H0 H1. rewrite E10 in H0, H1. rewrite Z.shiftl_mul_pow2 in H0, H1 by lia. change (2 ^ 32) with 4294967296 in H0, H1.
             apply ak4_SB; lia. }
    split; [exact ak4_PA|].
    split; [exact (ak4_hish_ceil HCEIL Hceil)|].
    split; [intros x Hx; apply ak5_space; lia|].
    split; [exact ak5_PA|].
    split; [exact (ak5_hish_ceil HCEIL Hceil)|].
    split; [exact ak6a|].
    split; [intros sc x Hin; destruct Hin|].
    split; [intros sc Hin; destruct Hin|].
    split; [exact ak8a_sh|].
    split; [exact ak8b_sh|].
    split; [exact ak8c_sh|].
    split; [intros x Hx; apply ak9; unfold ASegs.AIMG_LO, ASegs.AIMG_TOP in Hx; lia|].
    (* [comment removed for export] *)
    rewrite hsec_nil_st by reflexivity. cbn [zlen length map SecGap.zsum Z.of_nat]. rewrite !Z.add_0_r. unfold AHC0, AHL0.
    rewrite ak_maps. rewrite <- (firstn_skipn 18 (PM_MAPS brk0z X)). unfold zz2ww. rewrite map_app. fold (zz2ww (firstn 18 (PM_MAPS brk0z X))). fold (zz2ww (skipn 18 (PM_MAPS brk0z X))).
    rewrite hcnt_app, hlen_app.
    assert (LOW : Forall (fun e => KInv.ehi e <= AsShadow.AHI_LO) (zz2ww (skipn 18 (PM_MAPS brk0z X)))).
    { unfold PM_MAPS. cbn [skipn zz2ww map fst snd]. repeat constructor; vm_compute; discriminate. }
    rewrite (hcnt_low _ LOW), (hlen_low _ LOW), !Z.add_0_r.
    pose proof (hcnt_le_len (zz2ww (firstn 18 (PM_MAPS brk0z X)))) as C1. pose proof (hlen_le_total (zz2ww (firstn 18 (PM_MAPS brk0z X)))) as C2.
    revert C1 C2. unfold PM_MAPS, zlen. cbn [firstn zz2ww map fst snd length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite !AsMainVM.u_of_Z by lia. cbn [SecGap.zsum]. intros C1 C2.
    split. { split; [lia|]. split; [lia|]. intros sc Hin. destruct Hin. }
    (* [comment removed for export] *)
    intros a n Hband. apply GapGrid.region_free_introZ. intros e sz He.
    rewrite ak_noacc in He. unfold zz2ww in He. apply in_map_iff in He as [[b k] [Heq Hin]]. cbn [fst snd] in Heq. injection Heq as <- <-.
    pose proof (proj1 (Forall_forall _ _) zz_ok_noacc (b, k) Hin) as [Rb Rk]. cbn [fst snd] in Rb, Rk.
    rewrite !AsMainVM.u_of_Z by lia.
    pose proof (ak_sh_ceil HCEIL Hceil) as [SC1 SC2]. rewrite SC2 in Hband.
    assert (HB : (0x2008fff7000 <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= 0x10007fff8000)
                 \/ (0x80178800 <= bv_unsigned a /\ bv_unsigned a + bv_unsigned n <= 0x8fff6e00)).
    { destruct Hband as [[H1 H2]|[H1 H2]]; [left; lia | right].
      assert (SL : sh ASegs.AIMG_TOP = 0x80178800 /\ sh AsShadow.ALOWSH_LO = 0x8fff6e00) by (split; vm_compute; reflexivity).
      destruct SL as [SL1 SL2]. rewrite SL1 in H1. rewrite SL2 in H2. lia. }
    clear Hband SC1 SC2.
    pose proof al_R6 as (G61 & G62 & G63 & G64 & G65). pose proof al_PA as (G81 & G82 & G83 & G84 & G85). cbn [fst snd] in G61, G62, G63, G64, G65, G81, G82, G83, G84, G85.
    pose proof G_cases as GC.
    unfold PM_NOACC, PM_REM in Hin. rewrite !in_app_iff in Hin. cbn [In] in Hin.
    destruct Hin as [[Hin|[Hin|[Hin|[]]]]|[Hin|[Hin|[]]]].
    - injection Hin as <- <-.
      destruct GC as [(Hg & HM & HBk)|(Hg & HM & H19)]; rewrite HM.
      + lia.
      + pose proof (kp_facts _ _ H19) as (K1 & K2 & K3 & K4 & K5). cbn [fst snd] in K1, K2, K3, K4, K5. lia.
    - injection Hin as <- <-. pose proof (kp_facts _ _ kp_b08) as (_ & _ & _ & _ & K5). unfold X, Xof in K5 |- *. cbn [fst snd ps_b08] in K5 |- *. clear - HB K5. lia.
    - injection Hin as <- <-. pose proof (kp_facts _ _ kp_b06) as (_ & _ & _ & _ & K5). pose proof al_SB as (_ & T2 & T3 & _). unfold X, Xof in K5, T2, T3 |- *. cbn [fst snd ps_b06] in K5, T2, T3 |- *. clear - HB K5 T2 T3. lia.
    - destruct (pm_region_info X + 4096 <? ps_b06 X + 0x2000011000); cbn [In] in Hin; [|tauto]. destruct Hin as [Hin|[]]. injection Hin as <- <-.
      pose proof (kp_facts _ _ kp_b06) as (_ & _ & _ & _ & K5). pose proof al_SB as (_ & T2 & T3 & _). unfold X, Xof in K5, T2, T3 |- *. cbn [fst snd ps_b06] in K5, T2, T3 |- *. clear - HB K5 T2 T3. lia.
    - injection Hin as <- <-. clear - HB. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ri_accessible : forall x : word, pm_region_info X <= bv_unsigned x < pm_region_info X + 4096 ->
    in_rangesb x (vm_noaccess VMM) = false /\ in_rangesb x (zz2ww (PM_LAZY sp0z X)) = false.
  Proof.
    intros x Hx. pose proof al_SB as (S1 & S2 & S3 & S4 & S5 & S6). pose proof al_R6 as (G61 & G62 & G63 & G64 & G65). cbn [fst snd] in G61, G62, G63, G64, G65.
    pose proof (kp_apart_ne 2 3 _ _ ltac:(lia) kp_b06 kp_b08) as A68. pose proof (kp_apart_ne 2 11 _ _ ltac:(lia) kp_b06 kp_b22) as A622. cbn [fst snd] in A68, A622.
    pose proof G_cases as GC. pose proof (kp_facts _ _ kp_b06) as (_ & _ & B63 & _ & _). cbn [fst snd] in B63.
    split.
    - destruct (in_rangesb x (vm_noaccess VMM)) eqn:C; [exfalso|reflexivity].
      destruct (ak_noacc_cases x C) as [N|[N|[N|[N|N]]]]; try lia.
      (* [comment removed for export] *)
      destruct GC as [(Hg & HM & HB)|(Hg & HM & H19)]; rewrite HM in N; [lia|].
      pose proof (kp_apart_ne 2 17 _ _ ltac:(lia) kp_b06 H19) as A619. cbn [fst snd] in A619. lia.
    - apply (zz_out _ _ zz_ok_lazy). intros p Hp. unfold PM_LAZY, PM_REM in Hp. rewrite !in_app_iff in Hp. cbn [In] in Hp.
      destruct Hp as [[<-|[<-|[<-|[]]]]|[Hp|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; try lia.
      destruct (pm_region_info X + 4096 <? ps_b06 X + 0x2000011000); cbn [In] in Hp; [|tauto]. destruct Hp as [<-|[]]. cbn [fst snd]. lia.
  Qed.

  Theorem amaps_main : amaps_in_ledger s0 model.
  Proof.
    pose proof s0_k as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11). pose proof al_SB as (S1 & S2 & S3 & S4 & S5 & S6).
    pose proof (al_ceil HCEIL Hceil) as AC. pose proof (@aceil_range HCEIL) as AR. pose proof al_PA as (GP1 & GP2 & GP3 & _). cbn [fst snd] in GP1, GP2, GP3.
    unfold amaps_in_ledger. cbv zeta. change (a_st s0) with st0. rewrite E11, E7, E9. unfold kSpaceSize, kPageSize, kPtrArrayReserve.
    split. { (* [comment removed for export] *)
      intros mp Hin K1 K2 K3 K4. cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [mp_kind mp_base mp_size] in *.
      - split; [apply (ak_maps_exact (ps_b06 X) 0x2000011000); unfold PM_MAPS; cbn [In]; tauto| clear - S5 S6 AC AR; lia].
      - exfalso. exact (K1 eq_refl).
      - split; [apply (ak_maps_exact (ps_b08 X) 0x800000); unfold PM_MAPS; cbn [In]; tauto| clear - GP2 GP3 AC AR; lia]. }
    split. { intros mp Hin Hk x Hx. cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[]]]]; cbn [mp_kind mp_base mp_size] in *.
      - exfalso. destruct Hk as [Hk|[[c [Hk|Hk]]|Hk]]; discriminate Hk.
      - apply ri_accessible. rewrite S3. lia.
      - exfalso. destruct Hk as [Hk|[[c [Hk|Hk]]|Hk]]; discriminate Hk. }
    split; [intros sc x Hin; destruct Hin|].
    split; [exact ak_nooverlap | exact ak_nowrap].
  Qed.

  Theorem ashadow_main : ashadow_visible s0.
  Proof.
    unfold ashadow_visible. cbv zeta. change (a_st s0) with st0.
    split.
    - intros c x Hc Hx. rewrite (get_region_init (ps_b06 X) (pm_space_beg X) (ps_b08 X) env ts c) in Hx. cbn [rg_mapped_user region0] in Hx.
      change (0 / 8) with 0 in Hx. lia.
    - intros sc x Hin. cbn [as_sec cert_st0 init_state init_state_q] in Hin. destruct Hin.
  Qed.

End AT_MAIN.
