(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Open Scope Z_scope.

Lemma zxb_byte : forall fl, zxb (Z_to_bv 8 fl) = Z_to_bv 64 (fl mod 256).
Proof.
intros fl. apply bv_eq. unfold zxb. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. pose proof (Z.mod_pos_bound fl 256 ltac:(lia)).
rewrite (Z.mod_small (fl mod 256) (bv_modulus 64)); [reflexivity|]. change (bv_modulus 64) with (2^64). lia.
Qed.

Lemma land_mod256 : forall fl k, 0 <= k < 256 -> Z.land (fl mod 256) k = Z.land fl k.
Proof.
intros fl k Hk. change 256 with (2^8). rewrite <- (Z.land_ones fl 8) by lia.
rewrite <- Z.land_assoc. f_equal.
rewrite Z.land_comm. rewrite Z.land_ones by lia. apply Z.mod_small. change (2^8) with 256. lia.
Qed.

Lemma land_bit_cases : forall fl n, 0 <= n -> Z.land fl (2^n) = 0 \/ Z.land fl (2^n) = 2^n.
Proof.
intros fl n Hn. destruct (Z.testbit fl n) eqn:E; [right|left]; apply Z.bits_inj'; intros i Hi;
rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
- destruct (Z.eqb_spec n i) as [<-|NE]; [rewrite E; reflexivity | apply Bool.andb_false_r].
- rewrite Z.bits_0. destruct (Z.eqb_spec n i) as [<-|NE]; [rewrite E; reflexivity | apply Bool.andb_false_r].
Qed.

Lemma land16_cases : forall fl, Z.land fl 16 = 0 \/ Z.land fl 16 = 16.
Proof. intros fl. exact (land_bit_cases fl 4 ltac:(lia)). Qed.

Lemma land1_cases : forall fl, Z.land fl 1 = 0 \/ Z.land fl 1 = 1.
Proof. intros fl. exact (land_bit_cases fl 0 ltac:(lia)). Qed.

Lemma land2_cases : forall fl, Z.land fl 2 = 0 \/ Z.land fl 2 = 2.
Proof. intros fl. exact (land_bit_cases fl 1 ltac:(lia)). Qed.

Lemma land3_range : forall fl, 0 <= Z.land fl 3 <= 3.
Proof.
intros fl. pose proof (Z.land_ones fl 2 ltac:(lia)) as E. change (Z.ones 2) with 3 in E. rewrite E.
pose proof (Z.mod_pos_bound fl (2^2) ltac:(lia)). change (2^2) with 4 in *. lia.
Qed.

Lemma land3_split : forall fl, Z.land fl 3 = Z.land fl 1 + Z.land fl 2.
Proof.
intros fl.
assert (D : Z.land (Z.land fl 1) (Z.land fl 2) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.bits_0.
destruct (Z.eq_dec n 0) as [->|N0].
- change (Z.testbit 2 0) with false. rewrite !Bool.andb_false_r. reflexivity.
- replace (Z.testbit 1 n) with false; [rewrite Bool.andb_false_r; reflexivity|].
symmetry. change 1 with (2^0). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
rewrite (Z.add_nocarry_lxor _ _ D), (Z.lxor_lor _ _ D), <- Z.land_lor_distr_r. reflexivity.
Qed.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma wr_at_app : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
intros m a n1 n2 H1 H2. unfold wr_at. split.
- intros (Ha & Hb & H). repeat split; try lia; intros i Hi.
+ apply H. lia.
+ replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
- intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
intros i Hi. destruct (Z.lt_ge_cases i n1).
+ apply HA. lia.
+ replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.

#[using="Type"] Lemma rw_cells_app : forall m A cs1 cs2,
rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
intros m A cs1 cs2. unfold rw_cells, cells_at.
rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
rewrite wr_at_app by lia. rewrite bytes_at_app.
split.
- intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
rewrite (cells_bytes_length cs1 W1) in B2. tauto.
- intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

#[using="Type"] Lemma rw_cells_CB_cut : forall m A n bs k,
rw_cells segs m A [CB n bs] -> (k <= n)%nat ->
rw_cells segs m A [CB k (firstn k bs)] /\ rw_cells segs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
intros m A n bs k H Hk.
assert (L : length bs = n) by (destruct H as [[[Hwf _] _] _]; exact Hwf).
eapply rw_cells_split_CB with (pre := []) (post := []) (sizes := [k; (n - k)%nat]) in H; [| cbn; lia].
cbn [app mk_CB_cells] in H. rewrite firstn_skipn_comm in H.
replace (k + (n - k))%nat with n in H by lia. rewrite <- L, firstn_all in H. rewrite L in H.
change ([CB k (firstn k bs); CB (n - k) (skipn k bs)]) with ([CB k (firstn k bs)] ++ [CB (n - k) (skipn k bs)]) in H.
apply rw_cells_app in H. cbn [cells_size csize Nat.add] in H. rewrite Nat.add_0_r in H. exact H.
Qed.

#[using="Type"] Lemma rw_cells_CB_join : forall m A n1 n2 bs1 bs2,
rw_cells segs m A [CB n1 bs1] -> rw_cells segs m (A + Z.of_nat n1) [CB n2 bs2] ->
rw_cells segs m A [CB (n1 + n2) (bs1 ++ bs2)].
Proof.
intros m A n1 n2 bs1 bs2 H1 H2.
assert (L1 : length bs1 = n1) by (destruct H1 as [[[Hwf _] _] _]; exact Hwf).
assert (L2 : length bs2 = n2) by (destruct H2 as [[[Hwf _] _] _]; exact Hwf).
assert (E : rw_cells segs m A ([] ++ ([CB n1 bs1] ++ [CB n2 bs2]) ++ [])).
{ cbn [app]. change [CB n1 bs1; CB n2 bs2] with ([CB n1 bs1] ++ [CB n2 bs2]).
apply rw_cells_app. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. split; assumption. }
apply rw_cells_merge in E.
cbn [cells_size cells_bytes csize cbytes app Nat.add] in E. rewrite app_nil_r, Nat.add_0_r in E. exact E.
Qed.

End WithSegs.
