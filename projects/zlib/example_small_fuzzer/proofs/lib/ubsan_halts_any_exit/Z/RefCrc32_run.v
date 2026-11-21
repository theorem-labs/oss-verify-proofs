(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.ZChkCrc.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ListFacts.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.CrcBraid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32Base.

Module RefCrc32A.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.ZChkCrc.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ListFacts.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.CrcBraid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrcRod.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32Base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
Variable P : Z.
Hypothesis HP0 : 0 < P.


Section Pro.
Variable sp : Z.
Variable crc : Z.
Hypothesis Hsp : 80 <= sp <= 2 ^ 63.
Hypothesis Hcrc : 0 <= crc < 2 ^ 64.
End Pro.

Lemma magic20 : forall L, 0 <= L < 2 ^ 64 -> L * 14757395258967641293 / 2 ^ 68 = L / 20.
Proof.
  intros L HL.
  pose proof (Z.div_mod L 20 ltac:(lia)) as E. pose proof (Z.mod_pos_bound L 20 ltac:(lia)) as B.
  set (q := L / 20) in *. set (r := L mod 20) in *.
  symmetry. apply (Z.div_unique (L * 14757395258967641293) (2 ^ 68) q (L * 14757395258967641293 - 2 ^ 68 * q)); [left | lia].
  rewrite E. lia.
Qed.

Section Glue.
Variable spv : Z.
Hypothesis Hspv : 0 <= spv /\ spv + 80 <= 2 ^ 63.
End Glue.
End W.
End RefCrc32A.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32_run.RefCrc32A.

Module RefCrc32B.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.ZChkCrc.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ListFacts.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.CrcBraid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrcRod.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32Base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
Variable P : Z.
Hypothesis HP0 : 0 < P.

Local Ltac idx_range :=
  lazymatch goal with
  | |- 0 <= ?x mod 2 ^ 8 < 256 => pose proof (Z.mod_pos_bound x (2 ^ 8) ltac:(lia)); lia
  | |- 0 <= (?x mod 2 ^ 32) / ?m < 256 =>
      pose proof (Z.mod_pos_bound x (2 ^ 32) ltac:(lia));
      split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]
  end.

End W.
End RefCrc32B.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32_run.RefCrc32B.

Module RefCrc32C.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.ZChkCrc.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ListFacts.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.CrcBraid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrcRod.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32Base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
Variable P : Z.
Hypothesis HP0 : 0 < P.


Local Ltac hidef H := lazymatch type of H with ?T => change T with (hide T) in H end.

Section Combine.
Variable spv : Z.
Variable s1v : Z.
Variable s3v : Z.
Variable s8v : Z.
Variable s9v : Z.
Hypothesis Hspv : 0 <= spv /\ spv + 80 <= 2 ^ 64.
Hypothesis Hs1v : 0 <= s1v < 2 ^ 64. Hypothesis Hs3v : 0 <= s3v < 2 ^ 64.
Hypothesis Hs8v : 0 <= s8v < 2 ^ 64. Hypothesis Hs9v : 0 <= s9v < 2 ^ 64.
End Combine.
End W.
End RefCrc32C.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32_run.RefCrc32C.

Module RefCrc32T3.
From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.ZChkCrc.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ListFacts.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChkAdl.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32Base.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32Base.CrcBraid.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import CrcRod.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import DeflateLz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrcRod.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32Base.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefCrc32T2.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32T2.RefCrc32T1.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefCrc32T2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
Variable P : Z.
Hypothesis HP0 : 0 < P.
End W.
End RefCrc32T3.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefCrc32_run.RefCrc32T3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Set Warnings "-abstract-large-number".

Lemma align_count : forall P, 0 <= P -> exists k : nat,
  (k <= 3)%nat /\ (P + Z.of_nat k) mod 4 = 0 /\ (forall j, (j < k)%nat -> (P + Z.of_nat j) mod 4 <> 0).
Proof.
  intros Q HQ. pose proof (Z.mod_pos_bound Q 4 ltac:(lia)) as B. pose proof (Z.div_mod Q 4 ltac:(lia)) as E.
  set (r := Q mod 4) in *. set (q := Q / 4) in *.
  assert (C : r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
  destruct C as [C|[C|[C|C]]].
  - exists 0%nat. split; [lia|]. split; [|intros; lia].
    rewrite E, C. replace (4 * q + 0 + Z.of_nat 0) with (0 + q * 4) by lia. rewrite Z.mod_add by lia. reflexivity.
  - exists 3%nat. split; [lia|]. split.
    + rewrite E, C. replace (4 * q + 1 + Z.of_nat 3) with (0 + (q + 1) * 4) by lia. rewrite Z.mod_add by lia. reflexivity.
    + intros j Hj. rewrite E, C. replace (4 * q + 1 + Z.of_nat j) with ((1 + Z.of_nat j) + q * 4) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia.
  - exists 2%nat. split; [lia|]. split.
    + rewrite E, C. replace (4 * q + 2 + Z.of_nat 2) with (0 + (q + 1) * 4) by lia. rewrite Z.mod_add by lia. reflexivity.
    + intros j Hj. rewrite E, C. replace (4 * q + 2 + Z.of_nat j) with ((2 + Z.of_nat j) + q * 4) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia.
  - exists 1%nat. split; [lia|]. split.
    + rewrite E, C. replace (4 * q + 3 + Z.of_nat 1) with (0 + (q + 1) * 4) by lia. rewrite Z.mod_add by lia. reflexivity.
    + intros j Hj. rewrite E, C. replace (4 * q + 3 + Z.of_nat j) with ((3 + Z.of_nat j) + q * 4) by lia.
      rewrite Z.mod_add, Z.mod_small by lia. lia.
Qed.

Lemma combine_chain : forall l0 l1 l2 l3 l4 w0 w1 w2 w3 w4 q (X : Z),
  binv l0 l1 l2 l3 l4 q ->
  X = Z.lxor (xtnl 160 q) (comb5 w0 w1 w2 w3 w4) ->
  xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor (xtnl 32 (Z.lxor l0 w0)) (Z.lxor l1 w1))) (Z.lxor l2 w2))) (Z.lxor l3 w3))) (Z.lxor l4 w4))
  = X.
Proof.
  intros * HB HX. transitivity (combine l0 l1 l2 l3 l4 w0 w1 w2 w3 w4); [reflexivity|].
  rewrite (binv_combine _ _ _ _ _ _ w0 w1 w2 w3 w4 HB). symmetry. exact HX.
Qed.


Section W.
Variable P : Z.
Hypothesis HP0 : 0 < P.

Variable sp : Z.
Variable crc : Z.
Hypothesis Hsp : 80 <= sp <= 2 ^ 63.
Hypothesis Hcrc : 0 <= crc < 2 ^ 64.

Local Ltac fr1 F r := rewrite (F r) by reflexivity.

Section AfterPrologue.

Section AfterSaves.
End AfterSaves.
End AfterPrologue.




Lemma c0_of_eq : forall c, c0_of c = Z.lxor (wrap32 c) MASK32.
Proof.
  intros c. unfold c0_of, wrap32, MASK32. rewrite lxor_mod by lia.
  change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. reflexivity.
Qed.

End W.

