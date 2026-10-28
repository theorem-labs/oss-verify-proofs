(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX FakeStackRep
     AS_InstDefs N5_stack_malloc0 N5_stack_malloc2 N5_stack_malloc6 N5_stack_free6 N5_set_shadow_x.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section LawsX.
  Context {HCEIL : HeapCeil}.
  Variable p : iparams.
  Let RFS_is : forall LF m, as_RFS (KHp p) LF m <-> RFSI (as_FSB (KHp p)) LF m.
  Proof. intros LF m. cbn [as_RFS as_FSB KHp]. tauto. Qed.

  Lemma inst_stack_malloc_0 : stack_malloc_0_stmt (KHp p). Proof. exact (stack_malloc_0_ok (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_2 : stack_malloc_2_stmt (KHp p). Proof. exact (stack_malloc_2_ok (KHp p) RFS_is). Qed.
  Lemma inst_stack_malloc_6 : stack_malloc_6_stmt (KHp p). Proof. exact (stack_malloc_6_ok (KHp p) RFS_is). Qed.
  Lemma inst_stack_free_6 : stack_free_6_stmt (KHp p).   Proof. exact (stack_free_6_ok (KHp p) RFS_is). Qed.
  Lemma inst_set_shadow_00 : set_shadow_00_stmt.         Proof. exact set_shadow_00_ok. Qed.
  Lemma inst_set_shadow_f8 : set_shadow_f8_stmt.         Proof. exact set_shadow_f8_ok. Qed.
End LawsX.
