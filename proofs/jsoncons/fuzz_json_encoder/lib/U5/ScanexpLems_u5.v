(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import DecLemTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutCert Require Import Pm6CutKitD_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.FCutGen Require Import Cut_scanexp_xsrc_u5.
Import ListNotations. Import AX2. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Module SXL.
(* [comment removed for export] *)
Ltac lem_id := let E := fresh "E" in let M := fresh "M" in let HP := fresh "HP" in
  intros E M HP; first [exact (Forall_inv HP) | exact (Forall_inv (Forall_inv_tail HP)) | (cbn [kentry_ok edenot]; rewrite u_lit64; change two64 with (2 ^ 64); cbn; lia)].
(* [comment removed for export] *)
Ltac lem_mul := let E := fresh "E" in let M := fresh "M" in let HP := fresh "HP" in
  intros E M HP; DLT.prem_split HP; cbn [kentry_ok edenot] in *;
  repeat rewrite ?u_sltu64, ?u_slt64, ?u_add64, ?u_sub64, ?u_mul64, ?u_lit64, ?DLT.s_of_u in *;
  change two64 with (2 ^ 64) in *; DLT.gen_u;
  repeat match goal with H : context [(?a * ?b) mod 2 ^ 64] |- _ => rewrite (Z.mod_small (a * b) (2 ^ 64)) in * by (cbn; lia) end;
  repeat match goal with H : context [?a mod 2 ^ 64] |- _ => progress (rewrite (Z.mod_small a (2 ^ 64)) in * by (cbn; lia)) end;
  DLT.ifs; Z.div_mod_to_equations; lia.
End SXL.
Lemma lems_ok : LEMS_OK.
Proof.
  unfold LEMS_OK, CXD.LEMS_OK, LEMS.
  repeat (apply Forall_cons; [cbn [fst snd]; first [DLT.lem_enum | (unfold CXD.lemma_ok; SXL.lem_id) | (unfold CXD.lemma_ok; SXL.lem_mul) | (unfold CXD.lemma_ok; DLT.lem)] |]); apply Forall_nil.
Qed.
(* [comment removed for export] *)
Definition plans_ok := plans lems_ok.
Print Assumptions plans_ok.
