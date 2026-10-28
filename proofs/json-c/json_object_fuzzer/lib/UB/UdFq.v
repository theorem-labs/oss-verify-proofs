(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From Stdlib Require Import Sorting.Permutation.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition numch (c : Z) : bool :=
((48 <=? c) && (c <=? 57)) || (c =? 43) || (c =? 45) || (c =? 46) || (c =? 69) || (c =? 101).
Definition numb (b : byte) : bool := numch (bv_unsigned b).

#[using="Type"] Lemma lupd_same : forall {X} (ls : list X) i x, nth_error ls i = Some x -> lupd ls i x = ls.
Proof.
induction ls as [|y ls IH]; intros [|i] x H; cbn in *; try discriminate.
- injection H as ->. reflexivity.
- f_equal. apply IH. exact H.
Qed.

Section PbufcFacts.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma pbufc_agree : forall BS m m' PBS pb pre,
pbufc rsegs m PBS pb pre -> agree_on rsegs BS m m' -> incl PBS BS -> pbufc rsegs m' PBS pb pre.
Proof.
intros BS m m' PBS pb pre (buf & bpos & size & post & E & L & C) AG Hi. subst PBS.
exists buf, bpos, size, post. split; [reflexivity|]. split; [exact L|].
eapply pbuf_core_agree; [exact C | exact AG | apply Hi; left; reflexivity | apply Hi; right; left; reflexivity].
Qed.

#[using="Type"] Lemma pbufc_wtf : forall pf q LB0 ts A m m' md lo W pre,
PE_STATIC HIx pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
pbufc rsegs m (t_pbs ts) (t_pb ts) pre ->
munch W m m' -> wmono rsegs m m' -> Forall (pe_wtf pf) W ->
pbufc rsegs m' (t_pbs ts) (t_pb ts) pre.
Proof.
intros pf q LB0 ts A m m' md lo W pre STC HP PB MU WM HW.
eapply pbufc_agree; [exact PB | | apply incl_refl].
eapply (agree_wtf HIx); [exact STC | exact HP | exact MU | exact WM | exact HW |].
intros a n Hin. assert (HinL : In (a, n) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks, tstate_blocks; apply in_or_app; left; apply in_or_app; left; exact Hin).
split; [exact HinL|].
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold pe_blocks in ND.
intros ->. refine (nodup_app_ne _ _ _ _ _ _ ND _ _ eq_refl); [unfold tstate_blocks; apply in_or_app; left; exact Hin | left; reflexivity].
Qed.

#[using="Type"] Lemma pbufc_pres : forall LB SP m m' PBS pb pre,
pbufc rsegs m PBS pb pre -> heap_pres S4L LB SP m m' -> incl PBS LB -> pbufc rsegs m' PBS pb pre.
Proof.
intros LB SP m m' PBS pb pre PB HPR Hi.
eapply pbufc_agree; [exact PB | | exact Hi].
eapply (agree_of_heap_pres rsegs S4L); [exact HPR | reflexivity | intros b Hb; exact Hb].
Qed.
End PbufcFacts.

#[using="Type"] Lemma wview_static8 : forall m a,
(a = got_ssp \/ a = ssp_guard) ->
forall i, 0 <= i < 8 -> wview rsegs m (wa (a + i)) <> None.
Proof.
intros m a Ha i Hi.
assert (CASES : exists k : nat, (k < 8)%nat /\ i = Z.of_nat k) by (exists (Z.to_nat i); split; lia).
destruct CASES as (k & Hk & ->).
unfold wview. destruct (m (wa (a + Z.of_nat k))); [discriminate|].
destruct Ha as [-> | ->]; unfold got_ssp, ssp_guard;
do 8 (destruct k as [|k]; [vm_compute; discriminate|]); lia.
Qed.

#[using="Type"] Lemma ssp_cells_of_canary : forall m g,
bytes_at rsegs m got_ssp (le8 (Z_to_bv 64 ssp_guard)) -> bytes_at rsegs m ssp_guard (le8 g) ->
ssp_cells m g.
Proof.
intros m g B1 B2. split.
- split; [split; [cbn; repeat split; reflexivity | cbn [cells_bytes cbytes app pf_mxd]; rewrite app_nil_r; exact B1] |].
split; [unfold got_ssp; lia|]. split; [unfold got_ssp; cbn; lia|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ pf_mxd].
intros i Hi. apply wview_static8; [left; reflexivity | lia].
- split; [split; [cbn; repeat split; reflexivity | cbn [cells_bytes cbytes app pf_mxd]; rewrite app_nil_r; exact B2] |].
split; [unfold ssp_guard; lia|]. split; [unfold ssp_guard; cbn; lia|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ pf_mxd].
intros i Hi. apply wview_static8; [right; reflexivity | lia].
Qed.

#[using="Type"] Lemma Z_to_le_bytes_of_bytes : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes bytes_le_to_Z pf_mxd].
pose proof (bv_unsigned_in_range 8 b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (bytes_le_to_Z_nonneg bs) as Hnn.
rewrite lor_shiftl8_add by lia. f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) mod 256) with (bv_unsigned b); [reflexivity|].
Z.div_mod_to_equations. nia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
replace ((bv_unsigned b + 256 * bytes_le_to_Z bs) / 256) with (bytes_le_to_Z bs) by (Z.div_mod_to_equations; nia).
exact IH.
Qed.

#[using="Type"] Lemma le8_of_bytes : forall bs, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs L. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned. unfold bv_wrap.
pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8)) with (bv_modulus 64) in B.
pose proof (bytes_le_to_Z_nonneg bs).
rewrite Z.mod_small by lia. rewrite <- L. apply Z_to_le_bytes_of_bytes.
Qed.

Definition pe_frame_lo (segs : list Segment) (m : word -> option byte) (SPF : Z) (obj : Z) (c : byte) (j1 j2 : list byte) : Prop :=
rw_cells segs m SPF [C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 c].
Definition pe_frame_hi (segs : list Segment) (m : word -> option byte) (SPF : Z) (sv : pe_saved) : Prop :=
rw_cells segs m (SPF + 40)
[C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)].

#[using="Type"] Lemma pe_frame_split3 : forall m SPF obj cb j1 j2 utf sv,
pe_frame rsegs m SPF obj cb j1 j2 utf sv ->
pe_frame_lo rsegs m SPF obj cb j1 j2 /\ (exists w : word, le8 w = utf /\ rw_cells rsegs m (SPF + 32) [C8 w]) /\ pe_frame_hi rsegs m SPF sv.
Proof.
intros m SPF obj cb j1 j2 utf sv H. unfold pe_frame in H.
pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _ & L2 & _ & L8 & _).
change ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])
with ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb] ++ ([CB 8 utf] ++ [
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])) in H.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [H0 H]. apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [H1 H2].
cbn [cells_size csize Nat.add pf_mxd] in H1, H2.
replace (SPF + Z.of_nat 32) with (SPF + 32) in H1 by lia. replace (SPF + Z.of_nat 32 + Z.of_nat 8) with (SPF + 40) in H2 by lia.
split; [exact H0|]. split; [| exact H2].
exists (le_bytes_to_word utf). split; [apply le8_of_bytes; exact L8|].
eapply rw_cells_recast; [exact H1 | cbn; repeat split | cbn [cells_bytes cbytes app pf_mxd]; rewrite (le8_of_bytes utf L8); reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma pe_frame_join3 : forall m SPF obj cb j1 j2 (w : word) sv,
pe_frame_lo rsegs m SPF obj cb j1 j2 -> rw_cells rsegs m (SPF + 32) [C8 w] -> pe_frame_hi rsegs m SPF sv ->
pe_frame rsegs m SPF obj cb j1 j2 (le8 w) sv.
Proof.
intros m SPF obj cb j1 j2 w sv H0 H1 H2. unfold pe_frame_lo in H0. unfold pe_frame_hi in H2.
pose proof H0 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _ & L2 & _).
unfold pe_frame.
change ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 (le8 w);
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])
with ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb] ++ ([CB 8 (le8 w)] ++ [
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])).
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact H0|].
cbn [cells_size csize Nat.add pf_mxd]. replace (SPF + Z.of_nat 32) with (SPF + 32) by lia.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split.
- eapply rw_cells_recast; [exact H1 | cbn; repeat split; apply length_le8 | reflexivity | reflexivity].
- cbn [cells_size csize Nat.add pf_mxd]. replace (SPF + 32 + Z.of_nat 8) with (SPF + 40) by lia. exact H2.
Qed.

Definition pe_frame_rest (segs : list Segment) (m : word -> option byte) (SPF : Z) (c : byte) (j2 utf : list byte) (sv : pe_saved) : Prop :=
rw_cells segs m (SPF + 24)
[C4 (nbw j2); CB 3 (skipn 4 j2); C1 c; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)].

#[using="Type"] Lemma pe_frame_split_ret : forall m SPF obj cb j1 j2 utf sv,
pe_frame rsegs m SPF obj cb j1 j2 utf sv ->
rw_cells rsegs m SPF [C8 (Z_to_bv 64 obj)] /\
(exists wa wb : word, le8 wa ++ le8 wb = j1 /\ rw_cells rsegs m (SPF + 8) [C8 wa] /\ rw_cells rsegs m (SPF + 16) [C8 wb]) /\
pe_frame_rest rsegs m SPF cb j2 utf sv.
Proof.
intros m SPF obj cb j1 j2 utf sv H. unfold pe_frame in H.
pose proof H as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L1 & _).
change ([C8 (Z_to_bv 64 obj); CB 16 j1; C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])
with ([C8 (Z_to_bv 64 obj)] ++ ([CB 16 j1] ++ [C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])) in H.
apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [H0 H]. apply (proj1 (rw_cells_app rsegs _ _ _ _)) in H as [H1 H2].
cbn [cells_size csize Nat.add pf_mxd] in H0, H1, H2.
replace (SPF + Z.of_nat 8) with (SPF + 8) in H1 by lia. replace (SPF + Z.of_nat 8 + Z.of_nat 16) with (SPF + 24) in H2 by lia.
split; [exact H0|]. split; [| exact H2].
destruct (rw_cells_CB_cut rsegs _ _ _ _ 8 H1 ltac:(lia)) as [Ha Hb]. cbn [Nat.sub pf_mxd] in Hb. replace (SPF + 8 + Z.of_nat 8) with (SPF + 16) in Hb by lia.
assert (La : length (firstn 8 j1) = 8%nat) by (rewrite length_firstn; lia).
assert (Lb : length (skipn 8 j1) = 8%nat) by (rewrite length_skipn; lia).
exists (le_bytes_to_word (firstn 8 j1)), (le_bytes_to_word (skipn 8 j1)).
split; [rewrite (le8_of_bytes _ La), (le8_of_bytes _ Lb); apply firstn_skipn|]. split.
- eapply rw_cells_recast; [exact Ha | cbn; repeat split | cbn [cells_bytes cbytes app pf_mxd]; rewrite (le8_of_bytes _ La); reflexivity | reflexivity].
- eapply rw_cells_recast; [exact Hb | cbn; repeat split | cbn [cells_bytes cbytes app pf_mxd]; rewrite (le8_of_bytes _ Lb); reflexivity | reflexivity].
Qed.

#[using="Type"] Lemma pe_frame_join_ret : forall m SPF obj cb j2 utf (wa wb : word) sv,
rw_cells rsegs m SPF [C8 (Z_to_bv 64 obj)] -> rw_cells rsegs m (SPF + 8) [C8 wa] -> rw_cells rsegs m (SPF + 16) [C8 wb] ->
pe_frame_rest rsegs m SPF cb j2 utf sv ->
pe_frame rsegs m SPF obj cb (le8 wa ++ le8 wb) j2 utf sv.
Proof.
intros m SPF obj cb j2 utf wa wb sv H0 Ha Hb H2. unfold pe_frame_rest in H2.
pose proof H2 as [[Hwf _] _]. cbn in Hwf. destruct Hwf as (_ & L2 & _ & L8 & _).
unfold pe_frame.
change ([C8 (Z_to_bv 64 obj); CB 16 (le8 wa ++ le8 wb); C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])
with ([C8 (Z_to_bv 64 obj)] ++ ([CB 16 (le8 wa ++ le8 wb)] ++ [C4 (nbw j2); CB 3 (skipn 4 j2); C1 cb; CB 8 utf;
C8 (pe_s11 sv); C8 (pe_s10 sv); C8 (pe_s9 sv); C8 (pe_s8 sv); C8 (pe_s7 sv); C8 (pe_s6 sv);
C8 (pe_s5 sv); C8 (pe_s4 sv); C8 (pe_s3 sv); C8 (pe_s2 sv); C8 (pe_s1 sv); C8 (pe_s0 sv); C8 (pe_ra sv)])).
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact H0|]. cbn [cells_size csize Nat.add pf_mxd]. replace (SPF + Z.of_nat 8) with (SPF + 8) by lia.
apply (proj2 (rw_cells_app rsegs _ _ _ _)). split.
- eapply rw_cells_recast with (cs := [C8 wa; C8 wb]); [| cbn; repeat split; rewrite length_app, !length_le8; reflexivity | reflexivity | reflexivity].
change [C8 wa; C8 wb] with ([C8 wa] ++ [C8 wb]). apply (proj2 (rw_cells_app rsegs _ _ _ _)). split; [exact Ha|].
cbn [cells_size csize Nat.add pf_mxd]. replace (SPF + 8 + Z.of_nat 8) with (SPF + 16) by lia. exact Hb.
- cbn [cells_size csize Nat.add pf_mxd]. replace (SPF + 8 + Z.of_nat 16) with (SPF + 24) by lia. exact H2.
Qed.

Section CallFacts.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma PE_INVK_call : forall pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv m2 md2 A2 NB errv2,
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
heap_pres S4L (pe_blocks pf q LB0 ts) (pf_spf pf) m m2 ->
model_vm_only md md2 ->
HEAP S4L HIx A2 (NB ++ pe_blocks pf q LB0 ts) m2 md2 ->
stk rsegs m2 lo (pf_spf pf) ->
rw_cells rsegs m2 (0x77c00 - 164) [C4 errv2] ->
PE_INVK HIx pf q LB0 payload me lo m2 md2 A2 ts NB cb j1 j2 utf sv errv2.
Proof.
intros until errv2. intros STC [CORE REST] HPR VM HP2 ST2 ERR2.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * pf_mxd pf)) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
assert (AG : agree_on rsegs (pe_blocks pf q LB0 ts) m m2).
{ eapply (agree_of_heap_pres rsegs S4L); [exact HPR | reflexivity | intros b Hb; exact Hb]. }
split; [| split; [| split]].
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [| split; [| split; [exact Hpb | split]]].
+ eapply (heap_pres_rw_cells S4L); [exact HPR | exact TOK | eapply client_range_block; [exact INtk | lia | unfold tok_cells, tok_cells_g; cbn; lia]].
+ eapply pbuf_agree; [exact PB | exact AG |]. intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; left. exact Hb.
+ eapply (tstack_pres_g S4L); [exact HPR | exact INq | exact LEN32 | exact TSK].
+ eapply (heap_pres_rw_cells S4L); [exact HPR | exact FR | left; cbn; lia].
- eapply (PE_BASE_perm HIx); [| apply Permutation_app_comm].
eapply (PE_BASE_call HIx); [exact BASE | exact HPR | | exact VM | exact HP2 | exact ST2 | exact ERR2].
intros b Hb. unfold pe_blocks. apply in_or_app; right; right; right; exact Hb.
- intros i l Hl. eapply (lvl_cur_agree rsegs S4F); [exact (LV i l Hl) | exact AG |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hl.
- destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ].
eapply (jopt_agree rsegs S4F); [exact OBJ | exact AG |]. intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
Qed.

#[using="Type"] Lemma PE_BASE_stackcall : forall pf LB0 payload me lo m m' md A LBall errv errv' W,
PE_STATIC HIx pf lo ->
PE_BASE HIx pf LB0 payload me lo m md A LBall errv ->
incl LB0 LBall ->
munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf + PE_FRAME) \/ (fst iv = 0x77c00 - 164 /\ snd iv = 0x77c00 - 160)) W ->
stk rsegs m' lo (pf_spf pf) ->
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] ->
PE_BASE HIx pf LB0 payload me lo m' md A LBall errv'.
Proof.
intros until W. intros STC (HP & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG) Hincl MU WM MI HW ST' ERR'.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL). unfold alloc_ceiling, sp_window_lo, stack_max_size in LO.
assert (HW1 : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= hi_top S4L HIx)
\/ (exists a n, In (a, n) LBall /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch S4L x)) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H|[-> ->]]; cbn [fst snd pf_mxd] in *.
- left. unfold alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
- right; right. intros x Hx. cbn. lia. }
assert (HW2 : Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf + PE_FRAME)
\/ (exists a n, In (a, n) LBall /\ ~ In (a, n) LB0 /\ a <= fst iv /\ snd iv <= a + n)
\/ (forall x, fst iv <= x < snd iv -> hl_scratch S4L x)) W).
{ eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H|[-> ->]]; cbn [fst snd pf_mxd] in *.
- left. exact H.
- right; right. intros x Hx. cbn. lia. }
split; [| split; [exact ST' | split; [exact ERR' | split; [| split; [exact PLEN | split; [exact SBin | split; [| split; [exact MDV |]]]]]]]].
- eapply (heap_frame S4L HIx); [exact HP | | exact WM | exact MI]. eapply (frame_writes_ok S4L HIx); [exact HP | exact MU | exact HW1].
- eapply (payload_transport HIx); [exact STC | exact HP | exact Hincl | exact STR | exact PLEN | exact SBin | exact MU |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] Hiv. unfold payload_safe. cbn [fst snd hl_img_lo hl_img_hi S4L pf_mxd] in *.
destruct Hiv as [H1 | [E1 E2]].
+ left. unfold PE_FRAME, alloc_ceiling, sp_window_lo, stack_max_size in *. lia.
+ right; right. lia.
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch S4L s4_volatile LB0); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | exact Hincl | unfold PE_FRAME; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia | exact HW2].
- eapply jc_glob_P_munch; [exact JCG | exact MU | exact WM |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H|[-> ->]]; cbn [fst snd pf_mxd] in *; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Qed.

#[using="Type"] Lemma PE_INV_stackcall : forall pf q LB0 payload me lo m m' md A ts cb cb' j1 j1' j2 utf utf' sv errv errv' W,
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= pf_spf pf + PE_FRAME) \/ (fst iv = 0x77c00 - 164 /\ snd iv = 0x77c00 - 160)) W ->
stk rsegs m' lo (pf_spf pf) ->
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] ->
pe_frame rsegs m' (pf_spf pf) (t_obj ts) cb' j1' j2 utf' sv ->
PE_INV HIx pf q LB0 payload me lo m' md A ts cb' j1' j2 utf' sv errv' /\ heap_pres S4L (pe_blocks pf q LB0 ts) (pf_spf pf + PE_FRAME) m m'.
Proof.
intros until W. intros STC [CORE REST] MU WM MI HW ST' ERR' FR'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
apply (PE_REST_base HIx) in REST as (BASE & LV & OBJ).
pose proof (proj1 BASE) as HP.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * pf_mxd pf)) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
assert (HPRs : heap_pres S4L (pe_blocks pf q LB0 ts) (pf_spf pf + PE_FRAME) m m').
{ eapply (heap_pres_of_munch S4L); [exact MU | exact WM |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; exact Hb | unfold PE_FRAME; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia |].
eapply Forall_impl; [| exact HW]. intros [lo' hi'] [H|[-> ->]]; cbn [fst snd pf_mxd] in *; [left; exact H | right; right; intros x Hx; cbn; lia]. }
assert (AG : agree_on rsegs (pe_blocks pf q LB0 ts) m m') by (eapply (agree_of_heap_pres rsegs S4L); [exact HPRs | reflexivity | intros b Hb; exact Hb]).
split; [| exact HPRs]. split.
- split; [exact LEN32|]. split; [exact D32|]. split; [exact CO|]. split; [exact CHOFF|]. split; [| split; [| split; [exact Hpb | split; [| exact FR']]]].
+ eapply (heap_pres_rw_cells S4L); [exact HPRs | exact TOK | eapply client_range_block; [exact INtk | lia | unfold tok_cells, tok_cells_g; cbn; lia]].
+ eapply pbuf_agree; [exact PB | exact AG |]. intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; left. exact Hb.
+ eapply (tstack_pres_g S4L); [exact HPRs | exact INq | exact LEN32 | exact TSK].
- apply (PE_REST_of_base HIx).
+ eapply PE_BASE_stackcall; [exact STC | exact BASE | | exact MU | exact WM | exact MI | exact HW | exact ST' | exact ERR'].
intros b Hb. unfold pe_blocks. apply in_or_app; right; right; right; exact Hb.
+ intros i l Hl. eapply (lvl_cur_agree rsegs S4F); [exact (LV i l Hl) | exact AG |].
intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks l). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hl.
+ destruct (zin (cur_st ts) [ST_array_add; ST_ovadd]); [| exact OBJ].
eapply (jopt_agree rsegs S4F); [exact OBJ | exact AG |]. intros b Hb. unfold pe_blocks, tstate_blocks. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb.
Qed.

#[using="Type"] Lemma PE_INV_reframe : forall pf q LB0 payload me lo m mc md A ts cb cb' j1 j1' j2 j2' utf utf' sv errv x' co',
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
munch [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)] m mc -> wmono rsegs m mc -> mem_inv rsegs mc ->
rw_cells rsegs mc (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) (t_pb ts) (Z.of_nat (t_depth ts)) q x') ->
0 <= co' <= pf_len pf -> ts_choff x' = Z_to_bv 64 co' ->
pe_frame rsegs mc (pf_spf pf) (t_obj ts) cb' j1' j2' utf' sv ->
PE_INV HIx pf q LB0 payload me lo mc md A
(TST (t_depth ts) (t_levels ts) co' (t_pb ts) (t_pbs ts) x' (t_obj ts) (t_objs ts) (t_objbs ts)) cb' j1' j2' utf' sv errv.
Proof.
intros until co'. intros STC [CORE REST] MU WM MI TOK' Hco' CH FR'.
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
assert (HW : Forall (pe_wtf pf) [(pf_tk pf, pf_tk pf + 72); (pf_spf pf, pf_spf pf + PE_FRAME)]).
{ apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; cbn; lia | apply Forall_nil]. }
split.
- unfold PE_CORE; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [exact Hco'|]. split; [exact CH|].
split; [exact TOK'|]. split; [| split; [exact Hpb | split; [| exact FR']]].
+ eapply (pbuf_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW].
+ eapply (tstack_wtf HIx) with (ts := ts); [exact STC | exact (proj1 REST) | exact TSK | exact LEN32 | exact MU | exact WM | exact HW].
- eapply (PE_REST_private_write HIx) with (ts := ts) in REST; [exact REST | exact STC | exact MU | exact WM | exact MI | apply pe_wtf_private; exact HW].
Qed.

#[using="Type"] Lemma pe_pbs_sep : forall pf q LB0 ts A m md lo pb buf cap,
PE_STATIC HIx pf lo -> HEAP S4L HIx A (pe_blocks pf q LB0 ts) m md ->
t_pbs ts = [(pb, 16); (buf, cap)] ->
(pb + 16 <= buf \/ buf + cap <= pb) /\ (pf_tk pf + 72 <= pb \/ pb + 16 <= pf_tk pf) /\ (pf_tk pf + 72 <= buf \/ buf + cap <= pf_tk pf) /\
(q + (32 * pf_mxd pf) <= pb \/ pb + 16 <= q) /\ (q + (32 * pf_mxd pf) <= buf \/ buf + cap <= q).
Proof.
intros pf q LB0 ts A m md lo pb buf cap STC HP Epbs.
pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND.
assert (INtk : In (pf_tk pf, 72) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * pf_mxd pf)) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; right; right; left; reflexivity).
assert (INpbT : In (pb, 16) (tstate_blocks ts)) by (unfold tstate_blocks; rewrite Epbs; apply in_or_app; left; left; reflexivity).
assert (INbufT : In (buf, cap) (tstate_blocks ts)) by (unfold tstate_blocks; rewrite Epbs; apply in_or_app; left; right; left; reflexivity).
assert (INpb : In (pb, 16) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; left; exact INpbT).
assert (INbuf : In (buf, cap) (pe_blocks pf q LB0 ts)) by (unfold pe_blocks; apply in_or_app; left; exact INbufT).
unfold pe_blocks in ND.
assert (N1 : pb <> buf).
{ intros E. unfold tstate_blocks in ND. rewrite Epbs in ND. cbn [app map blk_addr fst pf_mxd] in ND.
apply List.NoDup_cons_iff in ND as [Hni _]. apply Hni. left. symmetry. exact E. }
assert (N2 : pb <> pf_tk pf) by (exact (nodup_app_ne _ _ _ _ _ _ ND INpbT ltac:(left; reflexivity))).
assert (N3 : buf <> pf_tk pf) by (exact (nodup_app_ne _ _ _ _ _ _ ND INbufT ltac:(left; reflexivity))).
assert (N4 : pb <> q) by (exact (nodup_app_ne _ _ _ _ _ _ ND INpbT ltac:(right; left; reflexivity))).
assert (N5 : buf <> q) by (exact (nodup_app_ne _ _ _ _ _ _ ND INbufT ltac:(right; left; reflexivity))).
split; [exact (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP INpb INbuf N1)|].
split; [pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP INpb INtk N2); lia|].
split; [pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP INbuf INtk N3); lia|].
split; [pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP INpb INq N4); lia|].
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ _ _ _ _ HP INbuf INq N5); lia.
Qed.
End CallFacts.
End RC__1.

Ltac tdok TDOK := first [ exact TDOK | exact (tdepth_ok_same _ _ eq_refl eq_refl eq_refl TDOK) ].
