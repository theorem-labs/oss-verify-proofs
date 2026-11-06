(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_leaves_memset.RTW_leaves_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Smear.
  Variable k : Z.
  Hypothesis Hk : 0 <= k.
  Definition topset (a y : Z) : Prop :=
    0 <= y /\ (forall i, 0 <= i -> a <= i <= k -> Z.testbit y i = true) /\ (forall i, k < i -> Z.testbit y i = false).

  Lemma topset_step : forall a c y, 0 < c -> a <= k - c + 1 -> topset a y -> topset (a - c) (Z.lor y (Z.shiftr y c)).
  Proof.
    intros a c y Hc Ha (Hy & H1 & H2). split; [| split].
    - apply Z.lor_nonneg. split; [exact Hy| apply Z.shiftr_nonneg; exact Hy].
    - intros i Hi Hr. rewrite Z.lor_spec, Z.shiftr_spec by lia.
      destruct (Z_le_gt_dec a i) as [L|L].
      + rewrite (H1 i) by lia. reflexivity.
      + rewrite (H1 (i + c)) by lia. apply orb_true_r.
    - intros i Hi. rewrite Z.lor_spec, Z.shiftr_spec by lia. rewrite (H2 i), (H2 (i + c)) by lia. reflexivity.
  Qed.

  Lemma topset_init : forall y, 0 < y -> Z.log2 y = k -> topset k y.
  Proof.
    intros y Hy Hl. split; [lia| split].
    - intros i Hi Hr. replace i with k by lia. rewrite <- Hl. apply Z.bit_log2. exact Hy.
    - intros i Hi. apply Z.bits_above_log2; lia.
  Qed.

  Lemma topset_full : forall a y, a <= 0 -> topset a y -> y = Z.ones (k + 1).
  Proof.
    intros a y Ha (Hy & H1 & H2). apply Z.bits_inj'. intros i Hi.
    destruct (Z_le_gt_dec i k) as [L|L].
    - rewrite (H1 i) by lia. rewrite Z.ones_spec_low by lia. reflexivity.
    - rewrite (H2 i) by lia. rewrite Z.ones_spec_high by lia. reflexivity.
  Qed.
End Smear.

Definition smear (S : Z) : Z :=
  let x1 := Z.lor S (Z.shiftr S 1) in
  let x2 := Z.lor x1 (Z.shiftr x1 2) in
  let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in
  let x5 := Z.lor x4 (Z.shiftr x4 16) in
  Z.lor x5 (Z.shiftr x5 32).

Lemma smear_val : forall S, 0 < S -> Z.log2 S <= 63 -> smear S = 2 ^ (Z.log2 S + 1) - 1.
Proof.
  intros S HS HL. replace (2 ^ (Z.log2 S + 1) - 1) with (Z.pred (2 ^ (Z.log2 S + 1))) by lia. rewrite <- Z.ones_equiv. set (k := Z.log2 S). pose proof (Z.log2_nonneg S) as K0. fold k in K0.
  unfold smear. cbv zeta.
  apply (topset_full k ltac:(lia) (k - 1 - 2 - 4 - 8 - 16 - 32)); [lia|].
  apply (topset_step k ltac:(lia) (k - 1 - 2 - 4 - 8 - 16) 32); [lia| lia|].
  apply (topset_step k ltac:(lia) (k - 1 - 2 - 4 - 8) 16); [lia| lia|].
  apply (topset_step k ltac:(lia) (k - 1 - 2 - 4) 8); [lia| lia|].
  apply (topset_step k ltac:(lia) (k - 1 - 2) 4); [lia| lia|].
  apply (topset_step k ltac:(lia) (k - 1) 2); [lia| lia|].
  replace (k - 1) with (k - 1) by lia.
  apply (topset_step k ltac:(lia) k 1); [lia| lia|].
  apply topset_init; [exact HS| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition popc_T (Y : Z) : Z :=
 ((Z.land
    ((Z.land
        ((Z.lxor Y 18446744073709551615 -
          Z.land (Z.shiftr (Z.lxor Y 18446744073709551615) 1) 6148914691236517205)
         mod 18446744073709551616)
        3689348814741910323 +
      Z.land
        (Z.shiftr ((Z.lxor Y 18446744073709551615 -
           Z.land (Z.shiftr (Z.lxor Y 18446744073709551615) 1) 6148914691236517205)
          mod 18446744073709551616)
         2)
        3689348814741910323 +
      Z.shiftr ((Z.land
          ((Z.lxor Y 18446744073709551615 -
            Z.land (Z.shiftr (Z.lxor Y 18446744073709551615) 1) 6148914691236517205)
           mod 18446744073709551616)
          3689348814741910323 +
        Z.land
          (Z.shiftr ((Z.lxor Y 18446744073709551615 -
             Z.land (Z.shiftr (Z.lxor Y 18446744073709551615) 1) 6148914691236517205)
            mod 18446744073709551616)
           2)
          3689348814741910323)
       mod 18446744073709551616)
      4)
     mod 18446744073709551616)
    1085102592571150095 *
  72340172838076673)
 mod 18446744073709551616).

Definition msb_ok (k : Z) : bool :=
  Z.eqb (Z.shiftr (popc_T (2 ^ (k + 1) - 1)) 56) (63 - k) && Z.eqb (Z.lxor (63 - k) 63) k.
Lemma msb_ok_all : forallb msb_ok (map Z.of_nat (seq 16 25)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma popc_T_val : forall k, 16 <= k <= 40 -> Z.shiftr (popc_T (2 ^ (k + 1) - 1)) 56 = 63 - k /\ Z.lxor (63 - k) 63 = k.
Proof.
  intros k Hk.
  assert (IN : In k (map Z.of_nat (seq 16 25))).
  { apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia. }
  pose proof (proj1 (forallb_forall _ _) msb_ok_all k IN) as H. unfold msb_ok in H.
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. auto.
Qed.

Lemma log2_range : forall S a b, 0 <= a -> 2 ^ a <= S < 2 ^ (b + 1) -> a <= Z.log2 S <= b.
Proof.
  intros S a b Ha HS. split.
  - apply Z.log2_le_pow2; lia.
  - assert (Z.log2 S < b + 1); [| lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MsbBlock.
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S : Z).
  Hypothesis HS : 2^16 <= S < 2^41.
  Variables (v0 v1 v2 v3 : word) (j1 : list byte) (nres nsc : Z) (j2 : list byte).
  Hypothesis NR : 0 <= nres < 2^64.
  Hypothesis SECC : rw_cells asegs m 0xa6c58 [C8 v0; C8 v1; C8 v2; C8 v3; CB 16 j1; C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsc); CB 552 j2].

  Lemma msb_block : forall (POST : machine_state -> Prop) x1 x2 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    mem_inv asegs m ->
    (forall y11 y12 y15 y16,
       evt asegs POST (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (wz 0xa6c58) x10 y11 y12 x13 (wz nres) y15 y16 x17 (wz S) (wz (63 - Z.log2 S)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (wz 0x36acc) fc None m (seg_rom asegs))) ->
    evt asegs POST (MS (mkR x1 x2 gp tp x5 x6 x7 x8 (wz 0xa6c58) x10 x11 x12 x13 x14 x15 x16 x17 (wz S) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F (wz 0x36a24) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros MI K. cbv beta delta [wz] in *.
    pose proof (log2_range S 16 40 ltac:(lia) ltac:(lia)) as LR.
    do 24 lstep. fl.
    match goal with |- context [Z_to_bv 64 (Z.lor ?a (Z.shiftr ?a 32))] => remember (Z.lor a (Z.shiftr a 32)) as Y eqn:EY end.
    assert (EY' : Y = 2 ^ (Z.log2 S + 1) - 1) by (rewrite EY; apply (smear_val S); lia).
    assert (YR : 0 <= Y < 2^41).
    { rewrite EY'. split; [apply Z.lt_le_pred; apply Z.pow_pos_nonneg; lia|].
      assert (2 ^ (Z.log2 S + 1) <= 2 ^ 41) by (apply Z.pow_le_mono_r; lia). lia. }
    clear EY.
    do 18 (lstep; fl).
    change (Z_to_bv 64 (Z.shiftr ?[t] 56)) with (Z_to_bv 64 (Z.shiftr (popc_T Y) 56)).
    rewrite EY', (proj1 (popc_T_val (Z.log2 S) LR)).
    apply K.
  Qed.
End MsbBlock.


End CeilWrap.
