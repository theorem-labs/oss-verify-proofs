(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaTuning Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Export LiaOrc.
Set Default Proof Mode "Classic".

Ltac orc_ff5_attemptA_ref :=
  ltac2:(Control.enter (fun () => let (l, s) := ff_disj_ids () in ff_clear_ids (List.append l s))); LiaTuning.zify_prune; lia_t12_ref.
Ltac orc_ff5_pqlia_ref :=
  first [ ltac2:(Control.enter (fun () => if ff_has_section_disj () then () else Control.zero (Tactic_failure None)));
          prune_disj; clear_mods; solve [ orc_ff5_attemptA_ref ]
        | prune_disj; clear_mods; lia_ref ].
Ltac orc_ff5_rlia_ref := clear_disj; repeat match goal with H : ~ _ |- _ => clear H end; clear_mods; LiaTuning.zify_prune; lia_t12_ref.
Ltac orc_ff5_ovl_ref A2 a :=
  ff_keep_near constr:((A2, a)); clear_mods; first [ LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker ].

Ltac orc_ff5_ovl0_ref := clear; Zify.zify; xlia zchecker.

Ltac orc_ff5_pqlia := orc_go_P ltac:(orc_ff5_pqlia_ref).
Ltac orc_ff5_rlia := orc_go_N ltac:(orc_ff5_rlia_ref).
(* [comment removed for export] *)
Ltac orc_ff5_overlap_ctx A2 n2 a len := assert_succeeds (assert (a < A2 + n2 /\ A2 < a + len) by (orc_go_O ltac:(orc_ff5_ovl_ref A2 a))).
Ltac orc_ff5_overlap A2 n2 a len :=
  let b1 := base_of A2 in let b2 := base_of a in constr_eq b1 b2;
  assert_succeeds (assert (a < A2 + n2 /\ A2 < a + len) by (orc_go_C ltac:(orc_ff5_ovl0_ref))).
