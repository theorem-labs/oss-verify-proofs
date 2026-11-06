(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec AgentLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPGVal AsanWordLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2 AX2S APC.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma land7_mod : forall z, 0 <= z -> Z.land z 7 = z mod 8.
Proof. intros. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma pgsel_arith : forall m x, 0 <= m < 8 -> 0 <= x < 2 ^ 64 ->
  (m + ((if m <? 1 then 1 else 0) * x) mod 2 ^ 64) mod 2 ^ 64 = (if m =? 0 then x else m).
Proof.
  intros m x Hm Hx. destruct (Z.eqb_spec m 0) as [->|NE].
  - cbn [Z.ltb]. rewrite Z.mul_1_l, Z.mod_small by lia. rewrite Z.mod_small by lia. reflexivity.
  - replace (m <? 1) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Z.mul_0_l, (Z.mod_small 0) by lia.
    rewrite Z.mod_small; lia.
Qed.
Lemma mod64_diff_zero' : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> (a - b) mod 2 ^ 64 = 0 -> a = b.
Proof. intros. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section S.
Variable SEGS : list Segment.

Lemma zero_diff_sound : forall E M k a b,
  know_ok SEGS E M k -> PGV.zero_diff k a b = true -> bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
Proof.
  intros E M k a b HK H. unfold PGV.zero_diff in H.
  destruct (erange k (mkAlu ALU_SUB a b)) as [[lo hi]|] eqn:Her; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst lo hi.
  pose proof (erange_sound SEGS E M k _ 0 0 HK Her) as Hz. rewrite mkAlu_denot in Hz. cbn [edenot] in Hz.
  rewrite u_sub64 in Hz. pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
  apply mod64_diff_zero'; lia.
Qed.

(* [comment removed for export] *)
Theorem partial_val_ok_sound : forall E M k ne v,
  know_ok SEGS E M k -> PGV.partial_val_ok k ne v = true ->
  bv_unsigned (edenot E ne) mod 8 <> 0 ->
  bv_unsigned (edenot E v) = bv_unsigned (edenot E ne) mod 8.
Proof.
  intros E M k ne v HK Tp Hr.
  set (n := bv_unsigned (edenot E ne)) in *. pose proof (u64_range (edenot E ne)) as Hn. fold n in Hn.
  pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as M8.
  enough (Hv' : bv_unsigned (edenot E (PGV.strip_b1 v)) = n mod 8).
  { destruct v as [| | | | | |sx lo w v'|]; try exact Hv'. destruct sx; [exact Hv'|].
    destruct lo as [|lo]; [|exact Hv']. destruct w as [|[|w]]; try exact Hv'.
    cbn [PGV.strip_b1] in Hv'. cbn [edenot]. unfold ext_val, ext_Z. rewrite Hv'.
    change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
    rewrite Z.div_1_r, (Z.mod_small (n mod 8) 256) by lia. apply zbv_u; lia. }
  unfold PGV.partial_val_ok in Tp. set (v' := PGV.strip_b1 v) in *.
  apply Bool.orb_prop in Tp. destruct Tp as [T1 | T2].
  - pose proof (zero_diff_sound E M k _ _ HK T1) as X. rewrite mkAlu_denot in X. cbn [edenot] in X.
    rewrite u_and64 in X. fold n in X. rewrite (u64_lit 7) in X by lia.
    rewrite land7_mod in X by lia. exact X.
  - destruct (PGV.pg_match v') as [[[ne1 ne2] X]|] eqn:Hpm; [|discriminate].
    apply andb_prop in T2 as [Z1 Z2].
    pose proof (zero_diff_sound E M k _ _ HK Z1) as X1. pose proof (zero_diff_sound E M k _ _ HK Z2) as X2.
    fold n in X1, X2.
    rewrite (PGV.pg_match_eq v' ne1 ne2 X Hpm). unfold PGV.pgsel2. cbn [edenot].
    rewrite u_add64, u_and64, u_mul64, u_sltu64, u_and64, X1, X2. rewrite !(u64_lit 7) by lia.
    rewrite (u64_lit 1) by lia. rewrite land7_mod by lia.
    pose proof (u64_range (edenot E X)) as RX.
    rewrite pgsel_arith by lia. replace (n mod 8 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hr). reflexivity.
Qed.
End S.
