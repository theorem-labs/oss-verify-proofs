(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.ZArith.BinInt.Z"; "le"; "@Corelib.Init.Datatypes"; "bool"; "true"; "@Corelib.Init.Logic"; "and"; "eq"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_main"; "chkD"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.SegD_states"; "SZMAX"; "SZMAXT"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB Require Import SegD_states SegD_main.
Require OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.
Open Scope Z_scope.

Lemma chkD_1 : chkD 1 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_2 : chkD 2 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_3 : chkD 3 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_4 : chkD 4 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_5 : chkD 5 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_6 : chkD 6 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_7 : chkD 7 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_8 : chkD 8 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_9 : chkD 9 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_10 : chkD 10 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma chkD_11 : chkD 11 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_12 : chkD 12 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_13 : chkD 13 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_14 : chkD 14 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_15 : chkD 15 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_16 : chkD 16 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_17 : chkD 17 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_18 : chkD 18 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_19 : chkD 19 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_20 : chkD 20 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_21 : chkD 21 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_22 : chkD 22 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_23 : chkD 23 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_24 : chkD 24 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_25 : chkD 25 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_26 : chkD 26 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_27 : chkD 27 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_28 : chkD 28 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_29 : chkD 29 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.
Lemma chkD_30 : chkD 30 = true.
Proof. OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.MemoFast.vmc. Qed.

Lemma chkD_allT : ltac2:(tb__ "0|0|
S5S3S0Z1R1A2S0R1S8A2A2S4S1S6R2A1S2A3F_;Fsz;").
Proof.
  intros sz H. unfold SZMAXT in H.
  assert (D : sz = 1 \/ sz = 2 \/ sz = 3 \/ sz = 4 \/ sz = 5 \/ sz = 6 \/ sz = 7 \/ sz = 8 \/ sz = 9 \/ sz = 10 \/ sz = 11 \/ sz = 12 \/ sz = 13 \/ sz = 14 \/ sz = 15 \/ sz = 16 \/ sz = 17 \/ sz = 18 \/ sz = 19 \/ sz = 20 \/ sz = 21 \/ sz = 22 \/ sz = 23 \/ sz = 24 \/ sz = 25 \/ sz = 26 \/ sz = 27 \/ sz = 28 \/ sz = 29 \/ sz = 30) by lia.
  destruct D as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; rewrite E;
  [exact chkD_1 | exact chkD_2 | exact chkD_3 | exact chkD_4 | exact chkD_5 | exact chkD_6 | exact chkD_7 | exact chkD_8 | exact chkD_9 | exact chkD_10 | exact chkD_11 | exact chkD_12 | exact chkD_13 | exact chkD_14 | exact chkD_15 | exact chkD_16 | exact chkD_17 | exact chkD_18 | exact chkD_19 | exact chkD_20 | exact chkD_21 | exact chkD_22 | exact chkD_23 | exact chkD_24 | exact chkD_25 | exact chkD_26 | exact chkD_27 | exact chkD_28 | exact chkD_29 | exact chkD_30].
Qed.

Lemma chkD_all : ltac2:(tb__ "0|0|
S5S3S0Z1R1A2S0R1S7A2A2S4S1S6R2A1S2A3F_;Fsz;").
Proof. intros sz H. apply chkD_allT. unfold SZMAX, SZMAXT in *. lia. Qed.
