(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia FunctionalExtensionality.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel InftreesCoverage.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Ext.
  Variables (lens1 lens2 : arr) (lens_ofs codes : Z).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hag : forall s, 0 <= s < codes -> arr_get lens1 (lens_ofs + s) = arr_get lens2 (lens_ofs + s).






  Lemma filter_ext_in : forall (f g : Z -> bool) (l : list Z), (forall x, In x l -> f x = g x) -> filter f l = filter g l.
  Proof.
    intros f g l H. induction l as [|x l IH]; [reflexivity|]. cbn. rewrite (H x) by (left; reflexivity).
    rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
  Qed.


  Hypothesis Hcodes1 : 1 <= codes.


  Variables (ty : codetype) (root table : Z).

End Ext.


Section Rel.
  Variables (ty : codetype) (lens1 lens2 : arr) (lens_ofs codes : Z) (tbl1 tbl2 : arr) (table bits : Z) (work1 work2 : arr).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hag : forall s, 0 <= s < codes -> arr_get lens1 (lens_ofs + s) = arr_get lens2 (lens_ofs + s).
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens1 (lens_ofs + s) <= 15.
  Hypothesis HtyC : ty = CODES -> codes <= 19 /\ bits = 7 /\ forall s, 0 <= s < codes -> arr_get lens1 (lens_ofs + s) <= 7.
  Hypothesis HtyD : ty = DISTS -> codes <= 32.
  Hypothesis Hbits : 1 <= bits <= 15.
  Hypothesis Htable : 0 <= table.
  Hypothesis Hroom1 : table + it_room ty <= arr_len tbl1.
  Hypothesis Hroom2 : table + it_room ty <= arr_len tbl2.
  Hypothesis Hwork1 : codes <= arr_len work1.
  Hypothesis Hwork2 : codes <= arr_len work2.

  Lemma Hlens2 : forall s, 0 <= s < codes -> 0 <= arr_get lens2 (lens_ofs + s) <= 15.
  Proof. intros s Hs. rewrite <- Hag by exact Hs. apply Hlens. exact Hs. Qed.

  Local Notation r1 := (inflate_table ty lens1 lens_ofs codes tbl1 table bits work1).
  Local Notation r2 := (inflate_table ty lens2 lens_ofs codes tbl2 table bits work2).
  Local Notation ret1 := (fst (fst (fst (fst r1)))).   Local Notation ret2 := (fst (fst (fst (fst r2)))).
  Local Notation tbl1' := (snd (fst (fst (fst r1)))).  Local Notation tbl2' := (snd (fst (fst (fst r2)))).
  Local Notation table1' := (snd (fst (fst r1))).     Local Notation table2' := (snd (fst (fst r2))).
  Local Notation bits1' := (snd (fst r1)).            Local Notation bits2' := (snd (fst r2)).

End Rel.
