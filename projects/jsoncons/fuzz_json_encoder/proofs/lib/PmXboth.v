(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec L5Defs HeapIface LibIface LibIfaceFp LibIfaceFpW HeapIfaceA HeapIfaceANull HeapIfaceN IcptIfaceA PmHeapIfaceA PmIcptIfaceA PmLibIfaceA PmLibIfaceAW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import Pm5IcptLayout Pm5ArtIfaceInst Pm5ArtIfaceInstX Pm5ArtIfaceInstN PmLibDefs PmLibSpecsX PmTopSpecsXW PmPhiX PmXbothFinalW PmXbothBaseW PmLibAssemblyXB PmInfraXB PmLibGlueXB.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Bridge Require Import PmHeapInst6.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmTop Require Import TopGlueXW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmInteg Require Import PmLibInstXW.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import AssemblyFullXBWF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PmXboth.
Definition PHI0 : list byte -> Prop := PmLibInstXW.PHI0.
Lemma phiw0 : PmTopSpecsXBW.TPSXAW.phiwP PHI0.
Proof. intros p H. exact H. Qed.

Section S.
#[local] Existing Instance PropExec.fx0.
Theorem xboth_base :
  strong_universal_error_free_T_scfg_budgets_abort PmXbothFinalW.cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  refine (PmXbothBaseW.xboth_base PHI0 (fun sp => TopGlueXW.Lay0 (bv_unsigned sp)) (fun _ => PMX.pm_staticsx) _ _ _ _ ASMXB.LayXA ASMXB.LStXA ASMXB.la1 ASMXB.la2 ASMXB.la3 _).
  - intros sp _. exact (TopGlueXW.Lay0_drv (bv_unsigned sp)).
  - exact PmLibInstXW.lib_iface0w.
  - intros sp _. exact TopGlueXW.pm_exit_ok.
  - exact TopGlueXW.Lay0_budget.
  - exact (ASMXB.la4w PmXbothFinalW.cfg0 PmXbothFinalW.art_IL PmXbothFinalW.art_ILX PmXbothFinalW.art_IL_ok PmXbothFinalW.art_ILX_ok PHI0
            (GLXB.libtopw PmXbothFinalW.cfg0 PmXbothFinalW.art_IL PmXbothFinalW.art_ILX PmXbothFinalW.art_IL_ok PmXbothFinalW.art_ILX_ok PHI0 phiw0)).
Qed.
(* [comment removed for export] *)
End S.
End PmXboth.
