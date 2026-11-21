(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc MallocCtrl PState KEv PTotal RSim FreshIface ProgC
  MF_Inv MF_Raw ModelInvC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.Malloc Require Import ProgDeps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition QF_kit : fkit.
Proof.
  refine (mkFK (fun X k cs => FF X k cs) _ _ _ _ _ _ _).
  - intros resv atop _. rewrite FF_strip. apply FF_init.
  - intros X Y k cs HP H. exact (FF_perm X Y k cs HP H).
  - intros X k k' cs Hk H. exact (FF_kle X k k' cs Hk H).
  - intros G X k n s0 HG Hn HP. exact (raw_malloc_specFP X G n k s0 HG Hn HP).
  - intros G X k p n HG. exact (raw_free_specFP X G p n k HG).
  - intros G X k n s mo HG HO HF Hn Hov HP HT. exact (raw_malloc_stotF X G n k s mo HG HO HF Hn Hov HP HT).
  - intros G X k p n s mo HG HO HF HT. exact (raw_free_stotF X G p n k s mo HG HO HF HT).
Defined.
