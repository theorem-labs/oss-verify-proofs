(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AllocWf AllocRep AS_InstWF AS_InstMainDefs.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsStartupHSF. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both Require Import AsMainState AsMainFacts AsMainLazy AsMainCells AsMainIface AsMainIfaceAlloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AsMainSyms. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.
Import ListNotations. Import AX2. Import AP. Import APS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)

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
  #[local] Notation pd_facts := (AsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).

  (* [comment removed for export] *)
  Variable HCEIL : HeapCeil.
  Hypothesis Hceil : hceil = sp0z - 8388608.
  Variables (env : list Z) (ts : bool) (AL0 : Z).
  #[local] Notation st0 := (cert_st0 X env ts).
  #[local] Notation s0 := (cert_s0 sp0z brk0z X env ts AL0).

  #[local] Notation T := (ps_b09 X).
  #[local] Notation CTX := (ps_b10 X).
  Ltac csz := cbn [cells_size csize cells_bytes cbytes le8 le4 le2 le1 word_to_le_bytes Z_to_le_bytes length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add app repeat map].
  Ltac geo := pose proof al_T as (GT1 & GT2 & GT3 & GT4 & GT5); pose proof al_CTX as (GC1 & GC2 & GC3 & GC4 & GC5);
              pose proof al_PA as (GP1 & GP2 & GP3 & GP4 & GP5); pose proof al_FSB as (GF1 & GF2 & GF3 & GF4 & GF5);
              pose proof al_SB as (S1 & S2 & S3 & S4 & S5 & S6); pose proof pd_facts as (PD1 & PD2 & PD3);
              cbn [fst snd] in GT1, GT2, GT3, GT4, GT5, GC1, GC2, GC3, GC4, GC5, GP1, GP2, GP3, GP4, GP5, GF1, GF2, GF3, GF4, GF5.

  Lemma s0_eqs : a_sb s0 = pm_space_beg X /\ a_ri s0 = pm_region_info X /\ a_pa s0 = ps_b08 X /\ a_thr s0 = T /\ a_ctx s0 = CTX
                 /\ a_fsb s0 = ps_b16 X /\ a_cache s0 = T + 208 /\ a_top s0 = pm_stack_top sp0z /\ a_bot s0 = pm_stack_bottom sp0z
                 /\ (forall c, RB s0 c = pm_space_beg X + Z.shiftl c 32) /\ (forall c, FA s0 c = pm_space_beg X + Z.shiftl c 32 + 0xE0000000)
                 /\ as_sec st0 = [] /\ as_n_reserved st0 = 0 /\ as_tq st0 = qcache0 /\ as_gq st0 = qcache0 /\ as_cache_inited st0 = false
                 /\ as_internal_init st0 = false /\ as_qmax st0 = kQuarantineMaxSize /\ as_qmin st0 = kQuarantineMinSize /\ as_qcache st0 = kMaxCacheSize.
  Proof.
    pose proof al_SB as (S1 & S2 & S3 & _). unfold a_ri, a_sb, a_pa, a_cache, RB, FA, free_array_base, region_beg, cert_s0, cert_st0.
    cbn [a_st a_thr a_ctx a_fsb a_top a_bot as_space_beg as_ptr_array as_sec as_n_reserved as_tq as_gq as_cache_inited as_internal_init as_qmax as_qmin as_qcache init_state init_state_q].
    unfold kSpaceSize, kRegionSizeLog, kFreeArrayOffset, OT_CACHE. repeat split; try reflexivity; try lia.
  Qed.
  Lemma s0_st : a_st s0 = st0.
  Proof. reflexivity. Qed.


  (* [comment removed for export] *)
  Lemma placed_main : placed_ok s0.
  Proof.
    geo. pose proof (al_ceil HCEIL Hceil) as AC. pose proof al_stack as (K1 & K2 & K3 & K4).
    unfold placed_ok, a_sb, a_pa, RB, FA, disj. cbn [a_st a_thr a_ctx a_fsb a_top a_bot cert_s0 cert_st0 as_space_beg as_ptr_array as_sec init_state init_state_q].
    unfold kSpaceSize, kPageSize, kPtrArrayReserve, AFS_SIZE. rewrite AC. unfold AsShadow.AHI_LO.
    assert (Hakobj : forall a n, geo (a, n) -> 0 <= n -> akobj a n).
    { intros a n (G1 & G2 & G3 & G4 & G5) Hn. cbn [fst snd] in G1, G2, G3, G4, G5. clear - G1 G2 G3 G4 G5 Hn AC.
      apply akobj_intro_sep; [lia | rewrite AC; lia | unfold ASegs.AIMG_LO, ASegs.AIMG_TOP; lia | unfold AsShadow.ALOWSH_LO, AsShadow.AHI_LO; lia]. }
    assert (Haapp : forall a n, geo (a, n) -> 0xF000 < n -> aapp a n).
    { intros a n G Hn. apply aapp_of_akobj_big; [apply Hakobj; [exact G | lia] | exact Hn]. }
    repeat match goal with |- _ /\ _ => split end.
    all: try (intros sc sc' Hin; destruct Hin). all: try (intros sc Hin; destruct Hin).
    all: try (apply Haapp; [first [exact al_PA | exact al_FSB] | lia]).
    all: try (apply Hakobj; [exact al_T | lia]).
    all: try (eapply aapp_sub; [apply Haapp; [exact al_CTX | lia] | lia | lia]).
    all: clear Hakobj Haapp.
    all: try (clear - S1 S2 S3 S4 S5 S6 GT1 GT2 GT3 GC1 GC2 GC3 GP1 GP2 GP3 GF1 GF2 GF3 PD1 PD2 PD3 K1 K2 K3 K4; (first [clear - S1 S5 S2 S6 S4 S3 GP1 GP3 GT1 GT3 GC1 GC3 GF3 K3 K4; (lia_guard; first [clear - S1 S5 S2 S6 S4 S3 GP1 GP3 GT1 GT3 GC1 GC3 GF3 K3 K4; (lia_guard; lia) | lia]) | (lia_guard; (lia_guard; lia))])).
    all: pose proof al_apart as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15); unfold zdisj in *.
    all: first [ (clear - A1 S2 S4; lia) | (clear - A2 S2 S4; lia) | (clear - A3 S2 S4; lia) | (clear - A4 S2 S4; lia)
               | (clear - A6; lia) | (clear - A7; lia) | (clear - A8; lia) | (clear - A10; lia) | (clear - A11; lia) | (clear - A13; lia) ].
  Qed.

  Lemma ast_ok_main : ast_ok s0.
  Proof. split; [exact placed_main | unfold cert_s0; cbn [a_st]; unfold cert_st0; apply WF_init]. Qed.

  (* [comment removed for export] *)
  Ltac junk_img := intros _; apply img_stk; lia.
  Lemma inst_rep_main : inst_rep s0 VM.
  Proof.
    destruct s0_eqs as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20).
    unfold inst_rep. cbv zeta. rewrite s0_st, E1, E2, E3, E12, E13, E15, E18, E19, E20.
    unfold AINST, OI_SPACEBEG, OI_NRESERVED, OI_SECMUTEX, OI_GSTATS, OI_Q, OI_QMAX, OI_QMUTEX, OI_GQ, OI_FBMUTEX, OI_MAXUSER,
      kPtrArrayReserve, kQuarantineMaxSize, kQuarantineMinSize, kMaxCacheSize, junk.
    cbn [qc_list qc_bytes qcache0 zlen length Z.of_nat map hd last].
    split; [exact in_hdr|]. split; [junk_img|]. split; [exact in_nreserved|]. split; [junk_img|]. split; [exact in_secmutex|].
    split; [junk_img|]. split; [junk_img|]. split; [exact in_quar|]. split; [junk_img|]. split; [exact in_qmutex|].
    split; [exact in_gq|]. split; [junk_img|]. split; [exact in_fbmutex|]. split; [junk_img|]. exact in_maxuser.
  Qed.

  Lemma flags_rep_main : flags_rep s0 VM.
  Proof.
    destruct s0_eqs as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20).
    unfold flags_rep. cbv zeta. rewrite s0_st, E5, E17.
    unfold AFLAGS, ACFLAGS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACANPOISON, AINITED, ACTXSIZE, ATSDINIT, AALLOCFLAGS, AIAINIT,
      AHOOKS, ADYING, AREALMEMSET, AMEMSET, AGOT_LO, AGOT_VALS, APAGESZ, ASECNAME, APRIMNAME, ATLSSLOT, ATSD, ALSANDIS, AGOT2. cbn [zbool].
    split; [exact fl_fill|]. split; [exact fl_psg|]. split; [exact fl_pp|]. split; [exact fl_ndtm|]. split; [exact fl_fastuw|].
    split; [exact fl_csmt|]. split; [exact fl_mmaplim|]. split; [exact fl_decorate|]. split; [exact fl_shbase|]. split; [exact fl_highend|].
    split; [exact fl_canpoison|]. split; [exact fl_inited|]. split; [exact fl_ctxsize|]. split; [exact fl_tsdinit|]. split; [exact fl_allocfl|].
    split; [exact fl_iainit|]. split; [exact fl_hooks|]. split; [exact fl_dying|]. split; [exact fl_realms|]. split; [exact fl_got|].
    split; [exact fl_pagesz|]. split; [exact fl_secname|]. split; [exact fl_primname|]. split; [exact fl_tlsslot|]. split; [exact fl_tsd|].
    split; [exact fl_lsandis | exact fl_got2].
  Qed.

  Lemma thread_rep_main : thread_rep s0 VM.
  Proof.
    destruct s0_eqs as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20).
    pose proof al_stack as (K1 & K2 & K3 & K4). geo.
    unfold thread_rep. cbv zeta. rewrite s0_st, E4, E5, E7, E8, E9, E14, K4.
    unfold OT_SWITCHING, OT_TQ, OT_CACHE, OT_STATS, OT_UNWINDING, CACHE_STATS, junk. cbn [qc_list qc_bytes qcache0 zlen length Z.of_nat map hd last].
    split; [exact th_ctx|]. split; [exact cx_tid|]. split; [exact cx_thr|]. split; [exact th_stack|]. split; [exact th_b40|]. split; [exact th_b40|].
    split; [exact th_tq|]. split; [intros _; apply th_stk80; lia|]. split; [intros _; apply th_stk80; lia|]. split; [intros _; apply th_stk80; lia|].
    exact th_unw.
  Qed.

  Lemma sec_rep_main : sec_rep s0 VM.
  Proof.
    destruct s0_eqs as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20).
    unfold sec_rep. cbv zeta. rewrite s0_st, E3, E12, E13. unfold wlist, junk, AsanAllocModel.zlen. cbn [map length]. change (Z.of_nat 0) with 0.
    rewrite !Z.add_0_r. split; [exact (proj1 pa_empty)|]. split; [intros H0; lia|]. intros [|i] hh Hn; discriminate Hn.
  Qed.

  Lemma ia_rep_main : ia_rep s0 VM.
  Proof.
    destruct s0_eqs as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20).
    unfold ia_rep. cbv zeta. rewrite s0_st, E17. unfold AIAINST. exact ia_main.
  Qed.

  (* [comment removed for export] *)
  Lemma classes_main : forall c, 0 <= c < kNumClasses ->
    region_rep s0 VM c /\ pclass_rep s0 VM c /\ region_shadow_rep s0 VM c /\ region_junk_rep s0 VM c.
  Proof.
    intros c Hc. unfold kNumClasses in Hc.
    destruct s0_eqs as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20).
    geo. pose proof (E10 c) as RBc. pose proof (E11 c) as FAc. rewrite Z.shiftl_mul_pow2 in RBc, FAc by lia. change (2 ^ 32) with 4294967296 in RBc, FAc.
    assert (GR : get_region st0 c = region0) by (unfold cert_st0; apply get_region_init).
    assert (GP : get_pc st0 c = pclass0) by (unfold cert_st0; apply get_pc_init).
    unfold region_rep, pclass_rep, region_shadow_rep, region_junk_rep. cbv zeta. rewrite s0_st, GR, GP, E2, E7, E16, RBc, FAc.
    cbn [rg_num_freed rg_mapped_free_array rg_allocated_user rg_mapped_user rg_free_array region0 pc_count pc_chunks pclass0 rev wlist map andb].
    unfold REGIONINFO_SIZE, PCLASS_SIZE, junk. rewrite !Z.add_0_r, ?Z.mul_0_r, ?Z.sub_0_r.
    split; [|split; [|split]].
    - (* [comment removed for export] *)
      split; [apply ri_cells0; [apply cells_wfb_sound; reflexivity | reflexivity | (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia]) | csz; (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])]|].
      split; [intros _; apply ri_stk; (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])|].
      split; [apply ri_cells0; [apply cells_wfb_sound; reflexivity | reflexivity | (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia]) | csz; (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])]|].
      split; [intros _; apply ri_stk; (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])|].
      split; [unfold u32arr, bytes_at, wr_at; cbn [u32s length Z.of_nat Z.mul flat_map]; repeat split; try (first [clear - S5 S2 Hc HC Hh Vfit Vev Vav Vbrk Vsp PD2 S6 S4 S3; lia | lia]); intros i Hi; lia|].
      split; intros H0; lia.
    - (* [comment removed for export] *)
      split; [apply th_cells0; [apply cells_wfb_sound; reflexivity | reflexivity | (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia]) | csz; (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])]|].
      split; [apply th_cells0; [apply cells_wfb_sound; reflexivity | reflexivity | (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia]) | csz; (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])]|].
      split; [unfold u32arr, bytes_at, wr_at; cbn [u32s length Z.of_nat Z.mul flat_map]; repeat split; try (first [clear - GT2 Hc HC Hh Vfit Vev Vav Vbrk Vsp PD2 GT3; lia | lia]); intros i Hi; lia|].
      intros _. apply th_stk80; (first [clear - Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia]).
    - (* [comment removed for export] *)
      split; [intros cp []|]. split; [intros cp []|].
      unfold poisoned, SHAD, poison_bytes, u8arr, bytes_at, wr_at, sh, ASHADOW_BASE.
      change (0 / 8) with 0. change (Z.to_nat 0) with 0%nat. cbn [repeat length Z.of_nat].
      split; (split; [(first [clear - S5 S2 Hc HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])|]; split; [(first [clear - S1 HC Hh Vfit Vev Vav Vbrk Vsp; lia | lia])|]; repeat split; try (first [clear - S5 S2 Hc HC Hh Vfit Vev Vav Vbrk Vsp PD2 S6 S4 S3; lia | lia]); intros i Hi; lia).
    - (* [comment removed for export] *)
      split; intros cp [].
  Qed.

  Theorem arep_main : AREP s0 VM.
  Proof.
    destruct s0_eqs as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20).
    unfold AREP. split; [exact ast_ok_main|]. split; [exact inst_rep_main|]. split; [exact flags_rep_main|]. split; [exact thread_rep_main|].
    split; [exact sec_rep_main|]. split; [exact ia_rep_main|]. split; [exact classes_main|].
    cbv zeta. rewrite s0_st, E14, E15. unfold cert_st0. rewrite chunk_list_init.
    split; [intros chk []|]. cbn [qc_list qcache0 batches_rep]. split; exact I.
  Qed.
End AT_MAIN.
