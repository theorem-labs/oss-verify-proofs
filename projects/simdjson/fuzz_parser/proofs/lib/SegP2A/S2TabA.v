(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import SjS2Tab.
From OSSVerify.simdjson.fuzz_parser.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SGA : list Segment := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma rdn_undefA : forall segs (m : word -> option byte) n (a : word), (forall j, (j < n)%nat -> m (a + Z_to_bv 64 (Z.of_nat j))%bv = None) ->
  rdn segs m a n = rdn segs (fun _ => None) a n.
Proof.
  intros segs m n. induction n as [|n IH]; intros a H; [reflexivity|].
  cbn [rdn].
  assert (H0 : m a = None).
  { specialize (H 0%nat ltac:(lia)). replace (a + Z_to_bv 64 (Z.of_nat 0))%bv with a in H; [exact H|].
    apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned. cbn [Z.of_nat]. change (bv_wrap 64 0) with 0. rewrite Z.add_0_r.
    symmetry. apply bv_wrap_bv_unsigned. }
  rewrite H0. rewrite (IH (a + 1)%bv); [reflexivity|].
  intros j Hj. replace (a + 1 + Z_to_bv 64 (Z.of_nat j))%bv with (a + Z_to_bv 64 (Z.of_nat (S j)))%bv; [apply H; lia|].
  apply bv_eq. rewrite !bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (bv_unsigned (1 : word)) with 1. rewrite Nat2Z.inj_succ. rewrite Zplus_mod_idemp_l. rewrite !Zplus_mod_idemp_r. f_equal. lia.
Qed.

Fixpoint bytes_eqbA (a b : list byte) : bool :=
  match a, b with [], [] => true | x :: a', y :: b' => (Z.eqb (bv_unsigned x) (bv_unsigned y) && bytes_eqbA a' b')%bool | _, _ => false end.
Lemma bytes_eqbA_eq : forall a b, bytes_eqbA a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply bv_eq in H1. rewrite H1, (IH _ H2). reflexivity.
Qed.

Definition d2v_chkA (i : nat) : bool :=
  match rdn SGA (fun _ => None) (Z_to_bv 64 (144960 + 4 * Z.of_nat i)) 4 with
  | Some bs => bytes_eqbA bs (word_to_le_bytes 4 (Z_to_bv 64 (d2v (Z.of_nat i))))
  | None => false
  end.

Lemma d2v_chkA_all : forallb d2v_chkA (seq 0 886) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma d2v_img_asan : forall m i, (forall x, 144960 <= x < 144960 + 3544 -> m (Z_to_bv 64 x) = None) -> 0 <= i < 886 ->
  rdn SGA m (Z_to_bv 64 (144960 + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (d2v i))).
Proof.
  intros m i HU Hi. rewrite rdn_undefA.
  - pose proof (proj1 (forallb_forall _ _) d2v_chkA_all (Z.to_nat i) ltac:(apply in_seq; lia)) as C.
    unfold d2v_chkA in C. rewrite Z2Nat.id in C by lia.
    destruct (rdn SGA (fun _ => None) (Z_to_bv 64 (144960 + 4 * i)) 4); [|discriminate]. f_equal. apply bytes_eqbA_eq. exact C.
  - intros j Hj. replace (Z_to_bv 64 (144960 + 4 * i) + Z_to_bv 64 (Z.of_nat j))%bv with (Z_to_bv 64 (144960 + 4 * i + Z.of_nat j)).
    + apply HU. lia.
    + apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      rewrite Z.add_mod_idemp_l by (cbn; lia). rewrite Zplus_mod_idemp_r. reflexivity.
Qed.
