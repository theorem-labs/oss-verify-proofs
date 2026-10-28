(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzInv.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil}.


(* [comment removed for export] *)
Section Read2.
  Variable segs : list Segment.
  Lemma le2_of_bytes : forall b0 b1 : byte,
    le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1)) = [b0; b1].
  Proof.
    intros b0 b1. pose proof (byte_urange b0). pose proof (byte_urange b1).
    unfold le2. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
    f_equal; [| f_equal]; apply bv_eq; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
      change (2 ^ Z.of_N 8)%Z with 256%Z.
    - replace (bv_unsigned b0 + 256 * bv_unsigned b1)%Z with (bv_unsigned b0 + bv_unsigned b1 * 256)%Z by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - rewrite Z.shiftr_div_pow2 by lia. change (2^8)%Z with 256%Z.
      replace (bv_unsigned b0 + 256 * bv_unsigned b1)%Z with (bv_unsigned b1 * 256 + bv_unsigned b0)%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by lia.
      rewrite Z.add_0_r. apply Z.mod_small. lia.
  Qed.
  Lemma u8arr_read2 : forall m A bs (i : Z) (b0 b1 : byte) a,
    u8arr segs m A bs ->
    nth_error bs (Z.to_nat (2 * i)) = Some b0 -> nth_error bs (Z.to_nat (2 * i + 1)) = Some b1 ->
    (0 <= i)%Z -> a = wa (A + 2 * i) ->
    ov_read_bytes segs m a 2 = Some (le2 (Z_to_bv 64 (bv_unsigned b0 + 256 * bv_unsigned b1))).
  Proof.
    intros m A bs i b0 b1 a [Hb _] N0 N1 Hi ->.
    pose proof (nth_error_lt _ _ _ N1) as L1.
    rewrite (bytes_at_read segs m A bs (2 * i) 2 Hb) by lia.
    rewrite le2_of_bytes. f_equal.
    cps_destruct (nth_error_split _ _ _ N0) as (pre & post & E & Hlen).
    replace (Z.to_nat (2 * i + 1)) with (Z.to_nat (2 * i) + 1)%nat in N1 by lia.
    rewrite E in N1. rewrite nth_error_app2 in N1 by lia. rewrite Hlen, Nat.add_comm, Nat.add_sub in N1.
    rewrite E, skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. cbn [skipn app].
    destruct post as [|x post']; cbn in N1; [discriminate|]. injection N1 as ->. reflexivity.
  Qed.
End Read2.

(* [comment removed for export] *)
Lemma lor_lt_pow2 : forall a b k, (0 <= a < 2 ^ k)%Z -> (0 <= b < 2 ^ k)%Z -> (0 <= Z.lor a b < 2 ^ k)%Z.
Proof.
  intros a b k Ha Hb.
  assert (N : (0 <= Z.lor a b)%Z) by (apply Z.lor_nonneg; lia).
  split; [exact N|].
  destruct (Z.eq_dec a 0) as [->|A]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B]; [rewrite Z.lor_0_r; lia|].
  assert (K : (0 <= k)%Z). { destruct (Z.neg_nonneg_cases k); [|lia]. rewrite Z.pow_neg_r in Ha by lia. lia. }
  assert (NZ : Z.lor a b <> 0%Z). { intros E. apply Z.lor_eq_0_iff in E. lia. }
  apply Z.log2_lt_pow2; [lia|].
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt; apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)

End ACeilS1.
