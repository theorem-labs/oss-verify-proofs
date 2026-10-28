(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanFast SegFastHavoc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import XIcptA_b XIcptAs0Kit_b.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module XIAF.
Definition xstep_g :=
  ltac:(let t := eval cbv beta delta [XIA.xstep XIA.xmemset XIA.xmemcpy XIA.xtls XIA.has_cells XIA.has_tcells XIA.shz_cover] in @XIA.xstep in
        SGF.has_const t (@APC.kn_havoc); SGF.has_const t (@APC.copy_facts); SGF.has_const t (@existsb); SGF.has_const t (@forallb);
        let t' := eval pattern (@APC.kn_havoc), (@APC.copy_facts), (@existsb), (@forallb) in t in
        lazymatch t' with ?F _ _ _ _ => exact F end).
Lemma xstep_g_ref : xstep_g (@APC.kn_havoc) (@APC.copy_facts) (@existsb) (@forallb) = @XIA.xstep.
Proof. reflexivity. Qed.
Definition xstep_f := xstep_g AX2H.kn_havocMF SGF.copy_factsM (@SGF.existsb_l) (@SGF.forallb_l).
Theorem xstep_f_eq : xstep_f = @XIA.xstep.
Proof. unfold xstep_f. rewrite AX2H.kn_havocMF_eq, SGF.copy_factsM_eq, SGF.existsb_l_eqf, SGF.forallb_l_eqf. exact xstep_g_ref. Qed.
End XIAF.

(* [comment removed for export] *)
Module XIAS0F.
Definition xstep_f : list SGP.region -> nat -> sym_state -> option sym_state :=
  XIAF.xstep_f AsanUbsan.M.loaded_segments XIA.AS0_MSET XIA.AS0_MCPY XIA.AS0_CELLS XIA.AS0_TLSPC XIA.AS0_TCELLS XIA.AS0_TPV XIA.AS0_ENTV XIA.AS0_CTXSLOT XIA.AS0_BLKSLOT.
Lemma xstep_f_eq : xstep_f = XIAS0.xstep.
Proof. unfold xstep_f, XIAS0.xstep. rewrite XIAF.xstep_f_eq. reflexivity. Qed.
End XIAS0F.
