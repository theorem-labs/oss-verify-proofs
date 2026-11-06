(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Layout Shadow Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf
  Zqc Zqd.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma rw_cells_merge_all : forall (m : mem) A cs, rw_cells asegs m A cs -> rw_cells asegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs H. pose proof (rw_cells_merge asegs m A [] cs []) as M. rewrite app_nil_r in M. cbn [app] in M. exact (M H).
Qed.

Lemma le2_le_bytes_to_word : forall bs : list byte, length bs = 2%nat -> le2 (le_bytes_to_word bs) = bs.
Proof.
  intros bs L. unfold le2, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with ((bytes_le_to_Z bs) mod 2^64)%Z.
  rewrite (Z_to_le_bytes_mod 2 _ 64) by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma cb2_c2 : forall (m : mem) A j, rw_cells asegs m A [CB 2 j] -> rw_cells asegs m A [C2 (le_bytes_to_word j)].
Proof.
  intros m A j H. apply num_cb2_c2. pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as [L _].
  rewrite (le2_le_bytes_to_word j L). exact H.
Qed.

Lemma zero_run_of_CB : forall (m : mem) A k, rw_cells asegs m A [CB k (repeat (Z_to_bv 8 0) k)] -> bytes_at asegs m A (repeat (Z_to_bv 8 0) k).
Proof.
  intros m A k H. pose proof (rw_cells_bytes_at asegs m A _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma shz_of_zcells : forall (m : mem) f c k, f mod 8 = 0 -> 0 <= f -> 2147450880 <= c ->
  rw_cells asegs m (f / 8 + c) [CB k (repeat (Z_to_bv 8 0) k)] -> shz m (f + 8 * (c - 2147450880)) (8 * Z.of_nat k).
Proof.
  intros m f c k F8 F0 C0 H. apply shz_run; [exact F8| exact F0| lia|].
  replace (f / 8 + 2147450880 + (c - 2147450880)) with (f / 8 + c) by lia. exact (zero_run_of_CB m _ k H).
Qed.

Lemma f64_8 : forall f, f mod 64 = 0 -> f mod 8 = 0.
Proof. intros f H. Z.div_mod_to_equations. lia. Qed.

Lemma f64_div : forall f k, f mod 64 = 0 -> (f + 8 * k) / 8 = f / 8 + k.
Proof. intros f k H. apply div8_add. exact (f64_8 f H). Qed.

Ltac asan_zc_hook :=
  match goal with
  | |- context [ov_read_bytes asegs ?m ?a 1] =>
      let Ea := addr_expr a in
      lazymatch Ea with
      | (?E / 8 + 2147450880)%Z =>
          match goal with
          | ZC : rw_cells asegs m (?f / 8 + ?c)%Z [CB ?k (repeat (Z_to_bv 8 0) ?k)] |- _ =>
              rewrite (shz_read m (f + 8 * (c - 2147450880))%Z (8 * Z.of_nat k)%Z E a
                         (shz_of_zcells m f c k ltac:(assumption) ltac:(lia) ltac:(lia) ZC)
                         ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(reflexivity))
          end
      end
  end;
  load_post.

Ltac asan_zcp_hook :=
  match goal with
  | |- context [ov_read_bytes asegs ?m ?a 1] =>
      let Ea := addr_expr a in
      match goal with
      | ZC : rw_cells asegs m ?S0 [CB ?k (repeat (Z_to_bv 8 0) ?k)] |- _ =>
          rewrite (zr_read1 m S0 k a (Ea - S0)%Z (zero_run_of_CB m S0 k ZC) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(unfold wa; f_equal; lia))
      end
  end;
  load_post.
