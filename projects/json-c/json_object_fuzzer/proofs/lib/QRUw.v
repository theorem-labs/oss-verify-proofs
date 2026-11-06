(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo_c1 QCcH Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo_c1.
Import QCcH Q0Ek.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Definition pbufc (m : word -> option byte) (BS : list blk) (pb : Z) (pre : list byte) : Prop :=
exists buf bpos size post,
BS = [(pb, PB_SZ); (buf, size)] /\
Z.of_nat (length pre) = bpos /\
pbuf_core segs m pb buf bpos size (pre ++ [Z_to_bv 8 0] ++ post).

#[using="Type"] Lemma pbufc_pbuf : forall m BS pb pre, pbufc m BS pb pre -> pbuf segs m BS pb.
Proof.
intros m BS pb pre (buf & bpos & size & post & E & L & C).
exists buf, bpos, size, pre, post. auto.
Qed.

#[using="Type"] Lemma pbuf_pbufc : forall m BS pb, pbuf segs m BS pb -> exists pre, pbufc m BS pb pre.
Proof.
intros m BS pb (buf & bpos & size & pre & post & E & L & C).
exists pre, buf, bpos, size, post. auto.
Qed.

#[using="Type"] Lemma pbufc_core_intro : forall m pb buf bpos size pre post,
Z.of_nat (length pre) = bpos ->
pbuf_core segs m pb buf bpos size (pre ++ [Z_to_bv 8 0] ++ post) ->
pbufc m [(pb, PB_SZ); (buf, size)] pb pre.
Proof. intros. exists buf, bpos, size, post. auto. Qed.

#[using="Type"] Lemma pbufc_firstn : forall bpos (pre post : list byte),
Z.of_nat (length pre) = bpos ->
firstn (Z.to_nat bpos) (pre ++ [Z_to_bv 8 0] ++ post) = pre.
Proof.
intros. rewrite firstn_app. replace (Z.to_nat bpos - length pre)%nat with 0%nat by lia.
rewrite firstn_all2 by lia. cbn. rewrite app_nil_r. reflexivity.
Qed.

End WithSegs.
End Mq0.
From Stdlib Require NArith.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Q6q3 QRjH QHnV QfLs QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs.
Import QgoP.
Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section WithL.
Variable L : heap_layout.
Notation segs := (hl_segs L).

Definition str_in_block (m : word -> option byte) (b n : Z) (bytes : list byte) (ds : Z) (str : list byte) : Prop :=
rw_cells segs m b [CB (Z.to_nat n) bytes] /\
b <= ds /\ ds + Z.of_nat (length str) + 1 <= b + n /\
firstn (length str + 1) (skipn (Z.to_nat (ds - b)) bytes) = str ++ [b0] /\
~ In b0 str.

#[using="Type"] Lemma rw_cells_bytes_at : forall m a n bs, rw_cells segs m a [CB n bs] -> bytes_at segs m a bs.
Proof. intros m a n bs [[[Hwf _] HB] _]. cbn in HB. rewrite app_nil_r in HB. exact HB. Qed.

#[using="Type"] Lemma bytes_at_sub : forall m a bs k j, bytes_at segs m a bs -> (k + j <= length bs)%nat ->
bytes_at segs m (a + Z.of_nat k) (firstn j (skipn k bs)).
Proof.
intros m a bs k j (Ha & Hl & H) Hkj. split; [lia|]. split; [rewrite length_firstn, length_skipn; lia|].
intros i Hi. rewrite length_firstn, length_skipn in Hi.
replace (a + Z.of_nat k + Z.of_nat i) with (a + Z.of_nat (k + i)) by lia. rewrite (H (k + i)%nat) by lia.
rewrite nth_error_firstn. replace (i <? j)%nat with true by (symmetry; apply Nat.ltb_lt; lia). rewrite nth_error_skipn. reflexivity.
Qed.

#[using="Type"] Lemma str_slack : forall (HIx : heap_iface L) A LB m md b n bytes ds str,
HEAP L HIx A LB m md -> In (b, n) LB -> str_in_block m b n bytes ds str ->
exists slack, bytes_at segs m ds (str ++ b0 :: slack) /\
(- (ds + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) /\
ds + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= b + n + 16.
Proof.
intros HIx A LB m md b n bytes ds str HP Hin (BLK & Hb & He & Hf & Hn).
pose proof (heap_blk L HIx _ _ _ _ b n HP Hin) as (Hn0 & Hal & Hb0 & Hbhi & _).
destruct (heap_blk_slack L HIx _ _ _ _ b n HP Hin) as [g [G Lg]].
assert (LENB : length bytes = Z.to_nat n) by (destruct BLK as [[[Hwf _] _] _]; exact Hwf).
pose proof (rw_cells_bytes_at _ _ _ _ BLK) as BB.

set (k := Z.to_nat (ds - b)).
pose proof (bytes_at_sub m b bytes k (length bytes - k) BB ltac:(lia)) as TAIL.
rewrite firstn_all2 in TAIL by (rewrite length_skipn; lia).
replace (b + Z.of_nat k) with ds in TAIL by lia.
assert (SPLIT : skipn k bytes = (str ++ [b0]) ++ skipn (length str + 1) (skipn k bytes)).
{ rewrite <- Hf. symmetry. apply firstn_skipn. }
exists (skipn (length str + 1) (skipn k bytes) ++ g). split; [|split].
- replace (str ++ b0 :: skipn (length str + 1) (skipn k bytes) ++ g) with (((str ++ [b0]) ++ skipn (length str + 1) (skipn k bytes)) ++ g)
by (rewrite <- !app_assoc; reflexivity).
apply bytes_at_app. split; [rewrite <- SPLIT; exact TAIL|].
rewrite <- SPLIT. rewrite length_skipn. replace (ds + Z.of_nat (length bytes - k)) with (b + n) by lia. exact G.
- rewrite length_app, !length_skipn, LENB.
replace (Z.of_nat (Z.to_nat n - k - (length str + 1) + length g)) with ((b + n - (ds + Z.of_nat (length str) + 1)) + Z.of_nat (length g)) by lia.
rewrite Lg.
set (x := ds + Z.of_nat (length str) + 1) in *.
pose proof (Z.div_mod n 16 ltac:(lia)) as E1. pose proof (Z.mod_pos_bound n 16 ltac:(lia)) as B1.
pose proof (Z.div_mod b 16 ltac:(lia)) as E2. rewrite Hal in E2.
pose proof (Z.div_mod (16 - n mod 16) 16 ltac:(lia)) as E3. pose proof (Z.mod_pos_bound (16 - n mod 16) 16 ltac:(lia)) as B3.
pose proof (Z.div_mod (- x) 8 ltac:(lia)) as E4. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as B4.
set (rn := n mod 16) in *. set (r8 := (- x) mod 8) in *.
set (qn := n / 16) in *. set (qb := b / 16) in *. set (q3 := (16 - rn) / 16) in *. set (q8 := - x / 8) in *.
nia.
- rewrite length_app, !length_skipn, LENB. pose proof (Z.mod_pos_bound (16 - n mod 16) 16 ltac:(lia)). lia.
Qed.
End WithL.

End RC__1.
End Mq2.

From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma v_sltiu_1 : forall (x : word) imm, 0 <= imm < 2^64 -> bv_unsigned x < imm -> v_sltiu x imm = Z_to_bv 64 1.
Proof. intros x imm Hi H. unfold v_sltiu, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
destruct (Z.ltb_spec (bv_unsigned x) imm); [reflexivity|lia]. Qed.
Lemma v_sltiu_0 : forall (x : word) imm, 0 <= imm < 2^64 -> imm <= bv_unsigned x -> v_sltiu x imm = Z_to_bv 64 0.
Proof. intros x imm Hi H. unfold v_sltiu, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
destruct (Z.ltb_spec (bv_unsigned x) imm); [lia|reflexivity]. Qed.
Lemma v_sltiu_iff : forall (x : word) imm, 0 <= imm < 2^64 ->
v_sltiu x imm = Z_to_bv 64 (if bv_unsigned x <? imm then 1 else 0).
Proof. intros x imm Hi. unfold v_sltiu, bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite Z.mod_small by lia.
destruct (bv_unsigned x <? imm); reflexivity. Qed.
Lemma v_slti_1 : forall (x : word) imm, zsig x < imm -> v_slti x imm = Z_to_bv 64 1.
Proof. intros x imm H. unfold v_slti. destruct (Z.ltb_spec (zsig x) imm); [reflexivity|lia]. Qed.
Lemma v_slti_0 : forall (x : word) imm, imm <= zsig x -> v_slti x imm = Z_to_bv 64 0.
Proof. intros x imm H. unfold v_slti. destruct (Z.ltb_spec (zsig x) imm); [lia|reflexivity]. Qed.
Lemma zsig_lit : forall z, -2^63 <= z < 2^63 -> zsig (Z_to_bv 64 z) = z.
Proof. intros z Hz. unfold zsig. apply Q9A7.Mq1.signed_of_Z. exact Hz. Qed.
Lemma v_sltu_1' : forall x y : word, bv_unsigned x < bv_unsigned y -> v_sltu x y = Z_to_bv 64 1.
Proof. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [reflexivity|lia]. Qed.
Lemma v_sltu_0' : forall x y : word, bv_unsigned y <= bv_unsigned x -> v_sltu x y = Z_to_bv 64 0.
Proof. intros x y H. unfold v_sltu, c_ltu, bv_ltu. destruct (Z.ltb_spec (bv_unsigned x) (bv_unsigned y)); [lia|reflexivity]. Qed.
Lemma v_slt_1 : forall x y : word, bv_signed x < bv_signed y -> v_slt x y = Z_to_bv 64 1.
Proof. intros x y H. unfold v_slt, c_lts, bv_lts. destruct (Z.ltb_spec (bv_signed x) (bv_signed y)); [reflexivity|lia]. Qed.
Lemma v_slt_0 : forall x y : word, bv_signed y <= bv_signed x -> v_slt x y = Z_to_bv 64 0.
Proof. intros x y H. unfold v_slt, c_lts, bv_lts. destruct (Z.ltb_spec (bv_signed x) (bv_signed y)); [lia|reflexivity]. Qed.

Ltac ub_nzpair p q :=
rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 p)) by (rewrite (unsigned_lit 0), (unsigned_lit p) by lia; lia);
rewrite (v_sltiu_0 (Z_to_bv 64 q) 1) by (rewrite ?(unsigned_lit q) by lia; lia).

Ltac ub_nowrap q p s :=
rewrite (v_sltu_0' (Z_to_bv 64 q) (Z_to_bv 64 p)) by (rewrite (unsigned_lit q), (unsigned_lit p) by lia; lia);
rewrite (v_slti_0 (Z_to_bv 64 s) 0) by (rewrite zsig_lit by lia; lia);
rewrite !(unsigned_lit 0) by lia; change (Z.lxor 0 0) with 0; rewrite (unsigned_lit 0) by lia; change (Z.lxor 0 1) with 1.

Lemma lxor_bound : forall a b n, 0 < n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lxor a b < 2^n.
Proof.
intros a b n Hn Ha Hb.
assert (H0 : 0 <= Z.lxor a b) by (apply (proj2 (Z.lxor_nonneg a b)); split; intros; lia).
split; [exact H0|].
destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hnz]; [lia|].
apply Z.log2_lt_pow2; [lia|].
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as HL.
assert (La : Z.log2 a < n) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
assert (Lb : Z.log2 b < n) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
lia.
Qed.
Lemma lxor_zero_iff : forall a b, Z.lxor a b = 0 <-> a = b.
Proof. intros a b. split; [apply Z.lxor_eq | intros ->; apply Z.lxor_nilpotent]. Qed.

Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64).
assert (Hl : Z.log2 x < 64) by (destruct (Z.eq_dec x 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
rewrite <- Z.ldiff_ones_l_low by lia. symmetry. apply Z.sub_nocarry_ldiff. apply Z.ldiff_ones_r_low; lia.
Qed.

Ltac ub_notltu p n :=
rewrite (unsigned_lit p) by lia; rewrite (lxor_ones64 p) by lia.
