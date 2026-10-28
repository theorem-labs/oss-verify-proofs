(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec KillFree HaltsKit HeapIface LibIface L5Defs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Bridge Require Import HeapInst0_u HeapClosed_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0DrvLibL_u Bs0DrvG_u Bs0DrvMain_u Bs0HeapBridge_u Bs0PmLayout_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout PnStatics PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u PnRunS_u PnTopS_u
     PnSHarness_u PnSHarnessStmts_u PnSExitCells_u BsonPmFinal_u
     PnStrS_u PnIssS_u PnSReaderCtor_u PnSysS_u PnLocS_u PnSSrcDtor_u PnSIosDtor_u Bs0Opdel_u Bs0Opnew_u PnSResetB_u PnSClose_u BsonPmPkgs_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ModeOn.
#[local] Existing Instance bm_on_inst | 0.

Definition PACKAGES_src_on : Prop := forall sptop, sptop_window sptop -> @PNH.harness_deps ScfgP_cfg0 _ (L0 sptop) (HI0 sptop).

(* [comment removed for export] *)
Theorem packages_src_on : PACKAGES_src_on.
Proof.
  intros sptop W.
  assert (LY : PMS.layout (L0 sptop)) by (apply pm_layout_L0; unfold sptop_window in W; lia).
  pose proof (HI0_ok_closed sptop cfg0 eq_refl) as HIok.
  pose proof (@L5NEW.opnew_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok) as OPN.
  pose proof (@L5DEL.opdel_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok) as OPD.
  pose proof (@PMLOC.locale_ctor_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok) as LCT.
  pose proof (@PMLOC.locale_dtor_ok ScfgP_cfg0 _ (L0 sptop)) as LDT.
  pose proof (@PMSID.ios_dtor_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok LDT) as IDT.
  constructor.
  - exact (@PMSTR.str_ctor_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok OPN).
  - exact (@PMISS.iss_ctor_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok LCT OPN).
  - exact (@PNSRC.reader_ctor_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok LCT OPN).
  - exact (@PMSYS.syscat_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok).
  - exact (@PNSRB.reset_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok).
  - exact (@PNSCL.parse_closed ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok).
  - exact OPD.
  - exact (@PMSSD.src_dtor_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok OPD LDT IDT).
  - exact LDT.
  - exact IDT.
Qed.

Lemma LIB0_on : forall sp, valid_sp sp ->
  lib_iface_ok (PNTS.TopLay (L0 (bv_unsigned sp))) cfg0 (HI0 (bv_unsigned sp)) PNTS.TopLS.
Proof.
  intros sp V. pose proof (valid_sp_window sp V) as W.
  assert (LY : PMS.layout (L0 (bv_unsigned sp))) by (apply pm_layout_L0; unfold sptop_window in W; lia).
  exact (@PNHT.harness_iface_ok ScfgP_cfg0 _ (L0 (bv_unsigned sp)) (HI0 (bv_unsigned sp)) LY (HI0_ok_closed (bv_unsigned sp) cfg0 eq_refl) (packages_src_on _ W)).
Qed.

(* [comment removed for export] *)
Lemma SRC_on : Bs0DrvMain_u.src_realizes_stmt2 cfg0 ShippedBudgets.lim_source.
Proof.
  exact (src0_realizes_spec_heap cfg0 eq_refl eq_refl
           (fun sp => PNTS.TopLay (HeapInst0_u.L0 (bv_unsigned sp))) (fun _ => PNTS.TopLS)
           drv_lib_layout_top0 LIB0_on (fun sp _ => PNSXC.top_lsx) budget0 ShippedBudgets.lim_source (or_introl eq_refl)).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem bson_pm_halts_plain :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source codes02
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
             Ubsan.M.phdrs).
Proof.
  intros [sp brk mb rnd] inp Hen Hvalid Hsw.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
  destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _).
  pose proof (SRC_on sp brk mb rnd inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds) as SRC.
  eapply (srealizes_init_must_exit (bmK := bm_on_inst) eq_refl cfg0).
  - exact SRC.
  - apply exit_codes_in_spec.
  - apply kill_free_spec.
  - exact Hsw.
Qed.
End ModeOn.
End FPX_1.
