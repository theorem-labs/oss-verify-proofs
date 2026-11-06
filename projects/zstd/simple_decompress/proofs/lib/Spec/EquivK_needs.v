(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Image.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim STree Malloc KInv JLedger Prog StepB EquivK_iface.
From OSSVerify.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

Definition cmalloc_contract2_stmt : Prop := forall csG csC J n,
  jcreach csG csC J -> 0 <= n -> jtree_ok J (cmalloc csG n) (cmalloc csC n) malloc_post2.

Definition cfree_contract2_stmt : Prop := forall csG csC J c,
  jcreach csG csC J -> In c (j_live J) -> jtree_ok J (cfree csG (Some c)) (cfree csC (Some c)) free_post2.

(* [comment removed for export] *)
Definition jcreach_atops_stmt : Prop := forall csG csC J,
  jcreach csG csC J -> s_atop csG = j_atopG J /\ s_atop csC = j_atopC J.

Definition live_bound_p_stmt : Prop := forall rs en inp,        (* [comment removed for export] *)
  valid_entry (mkImage psegs p_init_pc p_phdrs) en inp -> valid_input_either inp ->
  tlive LBND (Prog.prog psegs rs inp en) (mo0 psegs source_alloc_limit en inp).
Definition live_bound_u_stmt : Prop := forall rs en inp,
  valid_entry (mkImage usegs u_init_pc u_phdrs) en inp -> valid_input_either inp ->
  tlive LBND (Prog.prog usegs rs inp en) (mo0 usegs target_alloc_limit en inp).

  (* [comment removed for export] *)
