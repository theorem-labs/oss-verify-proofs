(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface LibIface L5Defs.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Bridge Require Import HeapInst0_u HeapClosed_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import Bs0PmLayout_u PnSpecsS_u PnRunS_u PnSHarnessStmts_u PnSHarness_u BsonPmFinal_u
     PnStrS_u PnIssS_u PnSReaderCtor_u PnSysS_u PnLocS_u PnSSrcDtor_u PnSIosDtor_u Bs0Opdel_u Bs0Opnew_u PnSResetB_u PnSClose_u.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition PARSE_S_stmt : Prop :=
  forall (L : heap_layout) (HI : heap_iface), PMS.layout L -> heap_iface_ok L cfg0 HI -> @PNRS.parse_spec ScfgP_cfg0 _ L HI.
Lemma parse_S : PARSE_S_stmt.
Proof. intros L HI LY HIok. exact (@PNSCL.parse_closed ScfgP_cfg0 _ L HI LY HIok). Qed.


Section Pkgs.

Theorem packages_src : PACKAGES_src.
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
  - exact (parse_S (L0 sptop) (HI0 sptop) LY HIok).
  - exact OPD.
  - exact (@PMSSD.src_dtor_ok ScfgP_cfg0 _ (L0 sptop) (HI0 sptop) LY HIok OPD LDT IDT).
  - exact LDT.
  - exact IDT.
Qed.


End Pkgs.
