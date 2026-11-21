(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad CMonad Harness.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.

Section HarnessC.
Context {St ptr : Type}.
Variable malloc : Z -> M St (option ptr).
Variable free : ptr -> M St unit.
Variables pre opt : list Z.

Definition fuzz_with (ps : list ptr) : M St Z := ps' <- alloc_all malloc opt ps ;; free_all free ps' ;;; mret 0.
Definition fuzz_without (ps : list ptr) : M St Z := free_all free ps ;;; mret 0.

Definition fuzz_one (data : list Z) : MC St Z :=
  cmbind (clift (alloc_all malloc pre []))
         (fun ps => if (length ps <? length pre)%nat
                    then clift (fuzz_without ps)
                    else cchoice (clift (fuzz_with ps)) (clift (fuzz_without ps))).

End HarnessC.
