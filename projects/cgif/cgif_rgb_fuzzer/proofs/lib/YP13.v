(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP14 YP15.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition DEPTH_MAX : Z := 8.
Definition COL_MAX : Z := Z.shiftl 1 DEPTH_MAX - 1.

Section a.
Variables W Hh : Z.
Hypothesis HW : 1 <= W < 2 ^ 16.
Hypothesis HH : 1 <= Hh < 2 ^ 16.
Hypothesis HN : W * Hh <= 10000.



End a.



Lemma chain_sizes : forall T', In T' ts_chain ->
In (T', 3 * T', 4 * T')
[(524309, 1572927, 2097236); (1048583, 3145749, 4194332); (2097169, 6291507, 8388676);
(4194319, 12582957, 16777276); (8388617, 25165851, 33554468); (16777216, 50331648, 67108864)] /\
4 * T' < 2 ^ 31 /\ 524288 <= T'.
Proof.
intros T' HT. cbv [ts_chain In] in HT.
repeat (destruct HT as [<-|HT]; [split; [cbv; tauto| cbv; split; [reflexivity| discriminate]]|]). destruct HT.
Qed.

Lemma resize_next : forall T, In T ts_chain -> T < MAX_TABLE_SIZE ->
In (getNextPrimePower2 T) ts_chain /\ T < getNextPrimePower2 T /\ ts_ok (getNextPrimePower2 T).
Proof.
intros T HT Hlt. split; [apply ts_chain_next; assumption|]. split; [apply ts_chain_next_gt; assumption|].
apply ts_chain_ok. apply ts_chain_next; assumption.
Qed.

Definition sizeLCT (cnt : Z) : Z := if COL_MAX <? cnt then COL_MAX else cnt.





Definition fcfg_attr (interlaced hasAlpha : bool) : Z :=
Z.lor (Z.lor 1 (if interlaced then 8 else 0)) (if hasAlpha then 2 else 4).






Definition RES_OK : Z := 0.        Definition RES_EALLOC : Z := 2.
Definition RES_PENDING : Z := 6.   Definition RES_ERROR : Z := 2 ^ 32 - 1.



