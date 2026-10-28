From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType State.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundR SymSummary.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout MallocLaws Contract.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJV BuilderDispose.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L4 Require Import S_bd.
Import ListNotations.
Open Scope Z_scope.

Lemma bd_chk_U : bd_chk_stmt U.Init.segsU bcU C_U EC_U.
Proof. unfold bd_chk_stmt. vm_compute. reflexivity. Qed.

Lemma bd_ejcert_U : bd_ejcert_stmt U.Init.segsU bcU EC_U.
Proof. unfold bd_ejcert_stmt. vm_compute. reflexivity. Qed.

Theorem builder_dispose_sum_U : builder_dispose_sum_stmt_U.
Proof. exact (BuilderDispose.builder_dispose_sum U.Init.segsU bcU C_U EC_U bd_chk_U bd_ejcert_U). Qed.

Theorem builder_dispose_sum_ex_U : builder_dispose_sum_ex_stmt_U.
Proof. exact (BuilderDispose.builder_dispose_sum_ex U.Init.segsU bcU C_U EC_U bd_chk_U bd_ejcert_U). Qed.
