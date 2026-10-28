(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel LazyRestrict LazyLedger LazySR BackingAlgebra.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AllocWf AllocRep AllocRepX AS_InstMainDefs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan AsHSTab AsStartupHSF AsMainVM. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazyChk AsMainLazy AsMainCells AsMainIface AsMainIfaceAlloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms.
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
  #[local] Notation Mr_some' := (AsMainIface.Mr_some' sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation vm_S := (AsMainIface.vm_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_full := (AsMainIface.vm_full sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VISZ0_eq := (AsMainLazy.VISZ0_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation KB := (AsMainLazy.KB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation KBAND_in := (AsMainLazy.KBAND_in sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation lazy_page_Z := (AsMainLazy.lazy_page_Z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation noacc_Z := (AsMainLazy.noacc_Z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation LM_Z := (AsMainLazy.LM_Z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VISZ_facts := (AsMainLazy.VISZ_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation ZR_low := (AsMainLazy.ZR_low sp0 brk0 h E) (only parsing).
  #[local] Notation ZR_high := (AsMainLazy.ZR_high sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vis_entry := (AsMainLazy.vis_entry sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation SW_ZR := (AsMainLazy.SW_ZR sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation lzc_parts := (AsMainLazy.lzc_parts h ch Hh) (only parsing).
  #[local] Notation KPS_placed := (AsMainLazy.KPS_placed sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pd_facts := (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  Variables (env : list Z) (ts : bool) (AL0 : Z).
  #[local] Notation s0 := (cert_s0 sp0z brk0z X env ts AL0).
  #[local] Notation MR := (Mr ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model FULL).
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kwr2 (bc : bctx) (qa : saddr) (qn : expr) (K : kentry) : bool :=
    match K with
    | KWr a n =>
        match lin_ofaB bc qa, lin_ofxB bc qn, lin_ofaB bc a, lin_ofxB bc n with
        | Some lq, Some lqn, Some l0, Some ln => le_linB bc l0 lq && le_linB bc lq l0 && le_linB bc lqn ln
        | _, _, _, _ => false end
    | _ => false
    end.
  (* [comment removed for export] *)
  Definition swin_ok (k : list kentry) (vis : list (expr * expr)) : bool :=
    let bc := mkbc k in
    forallb (fun p => let '(sb, sk, sn) := shadow_ofB ASAN_H bc (fst p) (snd p) in existsb (kwr2 bc (SA sb sk) sn) k) vis
    && match nth_error vis 5 with
       | Some p => let '(bb, bk) := split_lit (fst p) in existsb (kwr2 bc (SA bb bk) (snd p)) k
       | None => false end.
  Definition swin_check : bool := all_holes (fun g cls c => swin_ok (kn c) (a_vis c)).
  Lemma swin_check_ok : swin_check = true.
  Proof. vm_compute. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma kwr2_sound : forall qa qn K, In K (kn ch) -> kwr2 (mkbc (kn ch)) qa qn K = true ->
    exists lq lqn, lin_ofa (kn ch) qa = Some lq /\ lin_ofx (kn ch) qn = Some lqn /\ 0 <= lden E lq < 2 ^ 64 /\ lden E lq + lden E lqn <= 2 ^ 64
      /\ forall z, lden E lq <= z < lden E lq + lden E lqn -> 0xc04000 <= z -> exists b, FULL (wa z) = Some b.
  Proof.
    intros qa qn K HK HW. pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO.
    destruct K as [| | | | | | a n | | |]; try discriminate HW. cbn [kwr2] in HW.
    destruct (lin_ofaB (mkbc (kn ch)) qa) as [lq|] eqn:LQ; [|discriminate]. destruct (lin_ofxB (mkbc (kn ch)) qn) as [lqn|] eqn:LQN; [|discriminate].
    destruct (lin_ofaB (mkbc (kn ch)) a) as [l0|] eqn:L0; [|discriminate]. destruct (lin_ofxB (mkbc (kn ch)) n) as [ln|] eqn:LN; [|discriminate].
    apply andb_prop in HW as [HW H3]. apply andb_prop in HW as [H1 H2].
    rewrite lin_ofaB_eqf in LQ, L0. rewrite lin_ofxB_eqf in LQN, LN. rewrite le_linB_eqf in H1, H2, H3.
    pose proof (lin_ofa_sound _ _ _ _ KNF _ _ L0) as S0. pose proof (lin_ofx_sound _ _ _ _ KNF _ _ LN) as SN.
    apply (le_lin_sound _ _ _ _ KNF) in H1. apply (le_lin_sound _ _ _ _ KNF) in H2. apply (le_lin_sound _ _ _ _ KNF) in H3.
    exists lq, lqn. split; [exact LQ|]. split; [exact LQN|].
    cbn [kentry_ok] in KO. destruct KO as [FL ST]. unfold flat in FL. unfold elenZ in ST, FL. unfold uE in SN. rewrite SN in ST, FL.
    pose proof (lin_ofx_sound _ _ _ _ KNF _ _ LQN) as SQN. unfold uE in SQN. pose proof (u64_range (edenot E qn)) as RQN.
    split; [lia|]. split; [lia|]. intros z Hz Hhi.
    specialize (ST (z - estart E a) 1%nat ltac:(lia) ltac:(lia)). replace (estart E a + (z - estart E a)) with z in ST by lia.
    cbn [store_ok] in ST. fold (wa z) in ST.
    destruct (wview ASEGS MR (wa z)) as [b|] eqn:WV; [|discriminate].
    unfold wview in WV. destruct (MR (wa z)) as [b'|] eqn:HM.
    - exists b'. exact (Mr_some' _ _ HM).
    - exfalso. pose proof (asan_in_hull (wa z)) as NH. rewrite wa_unsigned in NH by lia. rewrite wa_unsigned in WV by lia.
      rewrite NH in WV; [discriminate|]. unfold APS.in_hull. cbn [img_lo img_hi ASAN_H]. apply andb_false_iff. right. apply Z.ltb_ge. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma swin_here : swin_ok (kn ch) (a_vis ch) = true.
  Proof. pose proof swin_check_ok as H. unfold swin_check in H. exact (AsMainCells.all_holes_here sp0 brk0 h ch Hh _ H). Qed.

  (* [comment removed for export] *)
  Lemma vis_window_full : forall p, In p (a_vis ch) ->
    forall z, SHOFF + uE E (fst p) / 8 <= z < SHOFF + uE E (fst p) / 8 + uE E (snd p) / 8 -> exists b, FULL (wa z) = Some b.
  Proof.
    intros p Hp z Hz. pose proof swin_here as SW0. unfold swin_ok in SW0. apply andb_prop in SW0 as [SW0 _].
    pose proof (proj1 (forallb_forall _ _) SW0 p Hp) as Hw. cbv beta in Hw.
    destruct (shadow_ofB ASAN_H (mkbc (kn ch)) (fst p) (snd p)) as [[sb sk] sn] eqn:Hsh. rewrite shadow_ofB_eqf in Hsh.
    apply existsb_exists in Hw as [K [HK HW]].
    destruct (kwr2_sound _ _ K HK HW) as (lq & lqn & LQ & LQN & B0 & B1 & FULLz).
    pose proof (lin_ofa_sound _ _ _ _ KNF _ _ LQ) as SQ. pose proof (lin_ofx_sound _ _ _ _ KNF _ _ LQN) as SQN.
    destruct (APS.shadow_of_den ASEGS ASAN_H (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) asan_shadow_ok 0%nat E MR (kn ch) (fst p) (snd p) sb sk sn KNF Hsh ltac:(rewrite SQ; lia)) as [D1 D2].
    cbn [shadow_off ASAN_H] in D1. unfold elenZ in D2.
    fold (uE E sn) in D2. fold (uE E (snd p)) in D2. fold (uE E (fst p)) in D1. rewrite SQ in D1. rewrite SQN in D2. unfold SHOFF in Hz.
    apply FULLz; [lia|]. pose proof (u64_range (edenot E (fst p))) as R1. unfold uE in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma b22_full : forall z, ps_b22 X <= z < ps_b22 X + 0x800000 -> exists b, FULL (wa z) = Some b.
  Proof.
    intros z Hz. pose proof swin_here as SW0. unfold swin_ok in SW0. apply andb_prop in SW0 as [_ SW0].
    pose proof (proj1 VISZ0_eq) as VE.
    destruct (nth_error (a_vis ch) 5) as [p|] eqn:Hn2; [|discriminate].
    apply (f_equal (fun l => nth_error l 5)) in VE. rewrite nth_error_map, Hn2 in VE. cbn [option_map] in VE. unfold VISZ0 in VE. cbn [nth_error] in VE.
    assert (P1 : uE E (fst p) = ps_b22 X) by congruence. assert (P2 : uE E (snd p) = 8388608) by congruence. clear VE.
    destruct (split_lit (fst p)) as [bb bk] eqn:Hsp.
    apply existsb_exists in SW0 as [K [HK HW]].
    destruct (kwr2_sound _ _ K HK HW) as (lq & lqn & LQ & LQN & B0 & B1 & FULLz).
    pose proof (lin_ofa_sound _ _ _ _ KNF _ _ LQ) as SQ. pose proof (lin_ofx_sound _ _ _ _ KNF _ _ LQN) as SQN.
    pose proof (APS.u_of_split E (fst p) bb bk Hsp ltac:(rewrite SQ; lia)) as UB.
    unfold uE in P1, P2, SQN. rewrite P2 in SQN.
    pose proof (kp_facts _ _ kp_b22) as (_ & G2 & _ & G4 & _). cbn [fst snd] in G2, G4.
    apply FULLz; [| lia]. rewrite <- SQ, <- UB, P1, <- SQN. lia.
  Qed.

  (* [comment removed for export] *)
  #[local] Notation GBAND_in := (AsMainLazy.GBAND_in sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  Lemma ghost_zero : forall q z, In q (GHZ X) -> SHOFF + fst q / 8 <= z < SHOFF + fst q / 8 + ((fst q + snd q) / 8 - fst q / 8) ->
    ~ zinP z (map (fun q => SW (fst q) (snd q)) (VISZ0 sp0z brk0z X)) -> FULL (wa z) = Some (b8 0).
  Proof.
    intros q z Hq Hz HnS.
    pose proof lz_facts as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6p & V10p & VSP).
    pose proof KB as KB0. cbv zeta in KB0. destruct KB0 as [_ KG]. pose proof (proj1 (Forall_forall _ _) KG q Hq) as [Bq1 Bq2]. cbv beta in Bq1, Bq2.
    pose proof (GBAND_in q Hq) as Bq3.
    pose proof pd_facts as (PD1 & PD2 & PD3).
    (* [comment removed for export] *)
    assert (HZ4 : (2201439137792 <= z < 17594333495296) \/ (2147446784 <= z < 2415882240)).
    { unfold SHOFF in Hz. clear - Hz Bq1 Bq2 Bq3 PD1 PD2. lia. }
    assert (Rz : 0 <= z < 2 ^ 64) by lia.
    pose proof (wa_unsigned z Rz) as Uz.
    assert (HLZ : zinP z (PM_LAZY sp0z X)).
    { unfold PM_LAZY. rewrite !AsMainLazy.zinP_app. cbn [AsMainLazy.zinP fst snd].
      clear - HZ4. destruct HZ4 as [H4|H4].
      - right. right. left. lia.
      - right. right. right. right. left. lia. }
    change (b8 0) with (Z_to_bv 8 0).
    apply (co_zero _ _ _ _ _ _ _ _ _ _ _ HC (wa z)); rewrite ?Uz.
    - (* [comment removed for export] *)
      unfold hid. apply orb_true_intro. right. apply negb_true_iff. unfold vis. rewrite Uz.
      replace (in_hull ASAN_H z) with false by (symmetry; unfold in_hull; apply andb_false_iff; right; apply Z.ltb_ge; change (img_hi ASAN_H) with 12599296; lia).
      replace (TOP model <=? z) with false by (symmetry; apply Z.leb_gt; rewrite TOPm; lia).
      cbn [orb]. apply andb_false_iff. right. apply orb_false_iff. split.
      + apply negb_false_iff. rewrite PM_lazy_eq, (AsMainLazy.page_in_ranges_zz sp0 brk0) by exact zz_ok_lazy. apply AsMainLazy.zpin_iff.
        unfold page_base, page_base_of. rewrite Uz. unfold page_size. rewrite u_of_Z by lia. apply lazy_page_Z. exact HZ4.
      + unfold in_allow. apply orb_false_iff. split.
        * destruct (in_vis E ch z) eqn:IV; [exfalso|reflexivity]. unfold in_vis in IV. apply existsb_exists in IV as [q' [Hq' Hb]].
          apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
          destruct (vis_entry q' ltac:(apply in_app_iff; left; exact Hq')) as (_ & _ & _ & HV).
          pose proof (proj1 (Forall_forall _ _) VISZ_facts _ HV) as VF1. cbn [fst snd] in VF1.
          clear - VF1 Hb1 Hb2 HZ4 PD1 PD2.
          destruct VF1 as [(F1 & F2 & F3 & F4) | [F | F]]; [lia | injection F as F1 F2; lia | injection F as F1 F2; lia].
        * destruct (in_sh ASAN_H E ch z) eqn:IS; [exfalso|reflexivity]. unfold in_sh in IS. apply existsb_exists in IS as [q' [Hq' Hb]].
          apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2. unfold sh_lo, sh_hi in Hb1, Hb2. cbn [fst snd] in Hb1, Hb2.
          replace (shadow_off ASAN_H) with SHOFF in Hb1, Hb2 by reflexivity.
          apply HnS. rewrite <- (proj1 VISZ0_eq). rewrite map_map.
          clear - Hq' Hb1 Hb2. induction (a_vis ch) as [|w V IH]; [destruct Hq'|]. cbn [map AsMainLazy.zinP]. destruct Hq' as [->|Hq']; [left | right; exact (IH Hq')].
          unfold SW. cbn [fst snd]. lia.
    - rewrite PM_maps_eq, (AsMainLazy.in_ivs_zz sp0 brk0) by exact zz_ok_maps. apply AsMainLazy.zin_iff. apply LM_Z. exact HLZ.
    - rewrite PM_noacc_eq, (AsMainLazy.in_ivs_zz sp0 brk0) by exact zz_ok_noacc. destruct (AsMainLazy.zin z (PM_NOACC brk0z X)) eqn:NA; [|reflexivity]. exfalso.
      apply AsMainLazy.zin_iff in NA. exact (noacc_Z _ HZ4 NA).
    - rewrite PM_lazy_eq, (AsMainLazy.page_in_ranges_zz sp0 brk0) by exact zz_ok_lazy. apply AsMainLazy.zpin_iff.
      unfold page_base, page_base_of. rewrite Uz. unfold page_size. rewrite u_of_Z by lia. apply lazy_page_Z. exact HZ4.
    - (* [comment removed for export] *)
      destruct (in_ghost E ch z) eqn:IG; [exfalso|reflexivity]. unfold in_ghost in IG. apply existsb_exists in IG as [q' [Hq' Hb]].
      apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
      destruct (vis_entry q' ltac:(apply in_app_iff; right; exact Hq')) as (_ & _ & _ & HV).
      pose proof (proj1 (Forall_forall _ _) VISZ_facts _ HV) as VF1. cbn [fst snd] in VF1. clear - VF1 Hb1 Hb2 HZ4 PD1 PD2.
      destruct VF1 as [(F1 & F2 & F3 & F4) | [F | F]]; [lia | injection F as F1 F2; lia | injection F as F1 F2; lia].
  Qed.


  (* [comment removed for export] *)
  Definition SWZ (q : Z * Z) : Z * Z := SW (fst q) (snd q).
  Theorem awin_main : awin_vis s0 VM.
  Proof.
    unfold awin_vis. cbn [a_S cert_s0]. intros x Hx.
    pose proof (u64_range x) as Rx. set (ux := bv_unsigned x) in *.
    assert (Ex : x = wa ux) by (unfold ux, wa; symmetry; apply bv_eq; rewrite Z_to_bv_unsigned; apply bv_wrap_small; apply bv_unsigned_in_range).
    rewrite (in_rangesb_zz _ x zz_ok_S) in Hx. fold ux in Hx. apply AsMainLazy.zin_iff in Hx.
    assert (VF : VM (wa ux) = FULL (wa ux)) by (apply vm_S; [exact Rx | exact Hx]).
    enough (DEF : exists b, FULL (wa ux) = Some b) by (destruct DEF as [b Hb]; rewrite Ex; unfold wview; rewrite VF, Hb; discriminate).
    unfold PM_S in Hx. cbn [AsMainLazy.zinP fst snd] in Hx. destruct Hx as [Hx|Hx]; [apply b22_full; exact Hx|].
    unfold VISZ in Hx. rewrite map_app, AsMainLazy.zinP_app in Hx.
    destruct (AsMainLazy.zin ux (map SWZ (VISZ0 sp0z brk0z X))) eqn:Z1.
    - (* [comment removed for export] *)
      apply AsMainLazy.zin_iff in Z1. clear Hx. rewrite <- (proj1 VISZ0_eq), map_map in Z1.
      assert (EXq : exists q, In q (a_vis ch) /\ fst (SWZ (uE E (fst q), uE E (snd q))) <= ux < fst (SWZ (uE E (fst q), uE E (snd q))) + snd (SWZ (uE E (fst q), uE E (snd q)))).
      { clear - Z1. induction (a_vis ch) as [|w V IH]; [destruct Z1|]. cbn [map AsMainLazy.zinP] in Z1. destruct Z1 as [Z1|Z1]; [exists w; split; [left; reflexivity | exact Z1] | destruct (IH Z1) as [q [Hq Hr]]; exists q; split; [right; exact Hq | exact Hr]]. }
      destruct EXq as [q [Hq Hr]]. unfold SWZ, SW in Hr. cbn [fst snd] in Hr.
      destruct (vis_entry q ltac:(apply in_app_iff; left; exact Hq)) as (HD & U1 & U2 & _).
      pose proof (AsMainLazy.DG_visg_len sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC _ HD) as (M0 & M1 & _). cbn [fst snd] in M0, M1.
      rewrite <- U1 in M1. rewrite <- U2 in M0. apply (vis_window_full q Hq). clear - Hr M0 M1. lia.
    - (* [comment removed for export] *)
      assert (Hout : ~ AsMainLazy.zinP ux (map SWZ (VISZ0 sp0z brk0z X))) by (intros Hc; apply AsMainLazy.zin_iff in Hc; congruence).
      destruct Hx as [Hx|Hx]; [exfalso; exact (Hout Hx)|].
      destruct (AsMainLazy.zinP_map_SW ux (GHZ X) Hx) as [q [Hq Hzq]]. unfold SW in Hzq. cbn [fst snd] in Hzq.
      rewrite (ghost_zero q ux Hq Hzq Hout). eexists; reflexivity.
  Qed.
End AT_MAIN.
