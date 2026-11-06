(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptNuma.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition NUMA_LUI : Z := 18446744073609551872.
Definition NUMA_K1 : Z := 18446744073609551615.     (* [comment removed for export] *)
Definition NUMA_K0 : Z := 18446744073609551616.     (* [comment removed for export] *)
Lemma numa_k1 : v_addi (Z_to_bv 64 18446744073609551872) (-257) = Z_to_bv 64 18446744073609551615.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma numa_k0 : v_addiw (Z_to_bv 64 18446744073609551872) (-256) = Z_to_bv 64 18446744073609551616.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma numa_addw : forall n, 0 <= n <= 100000000 ->
  v_addw (Z_to_bv 64 n) (Z_to_bv 64 18446744073609551615) = Z_to_bv 64 (18446744073609551615 + n).
Proof.
  intros n Hn. rewrite v_addw_Z. apply bv_eq. rewrite !u_Z2bv_mod. unfold sw32.
  replace ((n + 18446744073609551615 + 2 ^ 31) mod 2 ^ 32) with (n - 100000001 + 2 ^ 31).
  2:{ replace (n + 18446744073609551615 + 2 ^ 31) with ((n - 100000001 + 2 ^ 31) + 2 ^ 32 * 2 ^ 32) by lia.
      rewrite Z_mod_plus_full. rewrite Z.mod_small; lia. }
  replace (n - 100000001 + 2 ^ 31 - 2 ^ 31) with ((18446744073609551615 + n) + (-1) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma numa_n0_pos : forall n, 1 <= n <= 100000000 -> numa_n0 n = n.
Proof.
  intros n Hn. unfold numa_n0. replace (1 <=? n) with true by (symmetry; apply Z.leb_le; lia).
  replace (n <=? 100000000) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.
Lemma numa_n0_0 : numa_n0 0 = 50. Proof. reflexivity. Qed.
Lemma numa_n0_range : forall n, 0 <= n <= 20000 -> 1 <= numa_n0 n <= 20000.
Proof. intros n Hn. destruct (Z.eq_dec n 0) as [->|NZ]; [rewrite numa_n0_0; lia | rewrite numa_n0_pos by lia; lia]. Qed.

(* [comment removed for export] *)
Lemma keeps_cs_kept : forall R R', keeps R R' -> cs_kept R R'.
Proof.
  intros R R' K r Hr. apply K.
  destruct (cs_cases r Hr) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

Lemma mod16_mod8 : forall p, p mod 16 = 0 -> p mod 8 = 0.
Proof. intros p H. rewrite <- (Z.add_0_r p). apply mod16_plus_mod8; [exact H | reflexivity]. Qed.
Lemma mod16_mod4 : forall p, p mod 16 = 0 -> p mod 4 = 0.
Proof. intros p H. rewrite <- (Z.add_0_r p). apply mod16_plus_mod4; [exact H | reflexivity]. Qed.
