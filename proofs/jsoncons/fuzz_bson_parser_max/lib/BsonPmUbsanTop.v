(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface L5Defs KillFree.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BsonPmFinal BsonPmHalts Bs0DrvMain.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require BsonPmFinal_u BsonPmPkgs_u Bs0HeapBridge_u Bs0DrvMain_u PnTopS_u PnSExitCells_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U.CJ.Bridge Require HeapInst0_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Lemma TGT_ubsan : Bs0DrvMain_u.src_realizes_stmt2 BsonPmFinal_u.cfg0 target_alloc_limit.
Proof.
  exact (Bs0HeapBridge_u.src0_realizes_spec_heap BsonPmFinal_u.cfg0 eq_refl eq_refl
           (fun sp => PnTopS_u.PNTS.TopLay (HeapInst0_u.L0 (bv_unsigned sp))) (fun _ => PnTopS_u.PNTS.TopLS)
           BsonPmFinal_u.drv_lib_layout_top0 (BsonPmFinal_u.LIB0_of_packages BsonPmPkgs_u.packages_src)
           (fun sp _ => PnSExitCells_u.PNSXC.top_lsx) BsonPmFinal_u.budget0 target_alloc_limit
           ltac:(right; vm_compute; discriminate)).
Qed.

Theorem bson_pm_ubsan_final_abort :
  strong_universal_error_free_T_scfg_budgets_abort BsonPmFinal.cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  pose proof BsonPmHalts.SRC_on as SRC. pose proof TGT_ubsan as TGT.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid Hsw.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfit]]]. destruct Hent as [Hasp [Habrk [Hamb Hafit]]].
  destruct Hvalid as (Hargv & Henvp & Hfs & _ & Hcreds & _ & _ & Hhw & _).
  specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hrfit Hargv Henvp Hfs Hcreds).
  specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Hargv Henvp Hfs Hcreds).
  pose proof (srealizes_bm_transfer _ _ _ _ SRC ltac:(exact Hsw)) as SRC'. clear SRC.
  unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target in *.
  split; [| split].
  - eapply srealizes_error_free_unkilled; [exact SRC' | apply kill_free_spec].
  - eapply srealizes_error_free_unkilled; [exact TGT | apply kill_free_spec].
  - intro tr.
    rewrite (srealizes_traces_iff BsonPmFinal.cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC').
    rewrite (srealizes_traces_iff BsonPmFinal.cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
    reflexivity.
Qed.

End FPX_1.
