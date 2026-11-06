(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7.
Import ListNotations.
Open Scope Z_scope.

Lemma nodup_in_ne : forall (L P Q : list blk) a n b k,
Permutation L (P ++ Q) -> List.NoDup (map blk_addr L) -> In (a, n) P -> In (b, k) Q -> a <> b.
Proof.
intros L P Q a n b k HPm ND HP HQ ->.
apply (Permutation_map blk_addr) in HPm.
pose proof (Permutation_NoDup HPm ND) as ND'.
exact (nodup_prefix_suffix P Q b n k ND' HP HQ).
Qed.

Lemma nodup_app_l' : forall (BS LB : list blk), List.NoDup (map blk_addr (BS ++ LB)) -> List.NoDup (map blk_addr BS).
Proof. intros BS LB ND. rewrite map_app in ND. exact (NoDup_app_remove_r _ _ ND). Qed.
Lemma nodup_app_r' : forall (BS LB : list blk), List.NoDup (map blk_addr (BS ++ LB)) -> List.NoDup (map blk_addr LB).
Proof. intros BS LB ND. rewrite map_app in ND. exact (NoDup_app_remove_l _ _ ND). Qed.
