(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma fl_ok_sel : forall fl, fl_ok fl ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 fl)) 18446744073709551615)) ≫ 6))) 8 = 8.
Proof.
  intros fl [R H]. rewrite (unsigned_lit fl) by lia.
  assert (XB : 0 <= Z.lxor fl 18446744073709551615 < 2 ^ 64).
  { split; [apply Z.lxor_nonneg; lia|].
    destruct (Z.eq_dec (Z.lxor fl 18446744073709551615) 0) as [E|NE]; [rewrite E; lia|].
    apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lxor_nonneg fl 18446744073709551615) ltac:(lia)); lia|].
    pose proof (Z.log2_lxor fl 18446744073709551615 ltac:(lia) ltac:(lia)) as LL.
    assert (Z.log2 fl <= 63) by (destruct (Z.eq_dec fl 0) as [->|NF]; [cbn; lia| pose proof (proj1 (Z.log2_lt_pow2 fl 31 ltac:(lia)) ltac:(lia)); lia]).
    change (Z.log2 18446744073709551615) with 63 in LL. lia. }
  rewrite (unsigned_lit (Z.lxor fl 18446744073709551615)) by lia.
  assert (SB : 0 <= Z.lxor fl 18446744073709551615 ≫ 6 < 2 ^ 64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite (unsigned_lit _ SB).
  assert (B9 : Z.testbit fl 9 = false).
  { pose proof (f_equal (fun z => Z.testbit z 9) H) as T. cbv beta in T. rewrite Z.land_spec in T. change (Z.testbit 512 9) with true in T. change (Z.testbit 0 9) with false in T.
    rewrite andb_true_r in T. exact T. }
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.eq_dec n 3) as [->|NE].
  - rewrite Z.shiftr_spec by lia. change (3 + 6) with 9. rewrite Z.lxor_spec, B9. reflexivity.
  - change 8 with (2 ^ 3). rewrite (Z.pow2_bits_false 3 n) by lia. apply andb_false_r.
Qed.
