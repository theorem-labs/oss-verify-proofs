(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Image.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc KInv JLedger Prog StepB. From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import EquivK_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import TopLevel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PlainU0 Require Import UImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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

