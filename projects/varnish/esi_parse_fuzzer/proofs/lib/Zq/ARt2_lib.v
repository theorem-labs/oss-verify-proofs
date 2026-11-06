(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ox.F80_001.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Definition byte_at (m : mem) (a : Z) : byte := match m (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end.
Fixpoint rdbytes (m : mem) (a : Z) (n : nat) : list byte :=
  match n with O => [] | S n' => byte_at m a :: rdbytes m (a + 1) n' end.
Lemma rdbytes_length : forall m n a, length (rdbytes m a n) = n.
Proof. intros m n. induction n; intros a; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.
Lemma rdbytes_nth : forall m n a i, (i < n)%nat -> nth_error (rdbytes m a n) i = Some (byte_at m (a + Z.of_nat i)).
Proof.
  intros m n. induction n as [|n IH]; intros a i Hi; [lia|].
  destruct i as [|i]; cbn [rdbytes nth_error]. { rewrite Z.add_0_r. reflexivity. }
  rewrite IH by lia. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma mapped_rw_cells : forall m a n, mapped m a n -> 0 <= a -> 0 <= n -> a + n <= 2^64 ->
  rw_cells rsegs m a [CB (Z.to_nat n) (rdbytes m a (Z.to_nat n))].
Proof.
  intros m a n HM Ha Hn0 Hn.
  assert (BA : bytes_at rsegs m a (rdbytes m a (Z.to_nat n))).
  { split; [lia|]. split; [rewrite rdbytes_length; lia|].
    intros i Hi. rewrite rdbytes_length in Hi. rewrite rdbytes_nth by exact Hi.
    unfold mrd, wa, byte_at. destruct (m (Z_to_bv 64 (a + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
    exfalso. apply (HM (Z.of_nat i)); [lia| exact E]. }
  split; [split|].
  - cbn. rewrite rdbytes_length. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact BA.
  - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|].
    intros i Hi E. apply (HM i Hi). unfold wview, wa in E. destruct (m (Z_to_bv 64 (a + i))); [discriminate| reflexivity].
Qed.
Lemma mapped_junk : forall m a n, mapped m a n -> 0 <= a -> 0 <= n -> a + n <= 2^64 ->
  exists junk, rw_cells rsegs m a [CB (Z.to_nat n) junk].
Proof. intros. eexists. apply mapped_rw_cells; assumption. Qed.

Lemma mapped_sub : forall m a n b k, mapped m a n -> a <= b -> b + k <= a + n -> mapped m b k.
Proof. intros m a n b k HM H1 H2 i Hi. replace (b + i) with (a + (b - a + i)) by lia. apply HM. lia. Qed.

(* [comment removed for export] *)
Lemma bytes_mapped_rw : forall m a bs, bytes_at rsegs m a bs -> mapped m a (Z.of_nat (length bs)) ->
  rw_cells rsegs m a [CB (length bs) bs].
Proof.
  intros m a bs BA HM. destruct BA as (B0 & B1 & B2).
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [exact B0|]. split; [exact B1|]. exact B2.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi E. apply (HM i Hi). unfold wview, wa in E. destruct (m (Z_to_bv 64 (a + i))); [discriminate| reflexivity].
Qed.
Lemma bytes_mapped_C8 : forall m a (v : word), bytes_at rsegs m a (le8 v) -> mapped m a 8 -> rw_cells rsegs m a [C8 v].
Proof.
  intros m a v BA HM. pose proof (bytes_mapped_rw m a (le8 v) BA ltac:(rewrite length_le8; exact HM)) as H.
  rewrite length_le8 in H. destruct H as [[_ B] W]. split; [split; [exact (conj I I)| exact B]| exact W].
Qed.
Lemma bytes_mapped_C1 : forall m a (b : byte), bytes_at rsegs m a [b] -> mapped m a 1 -> rw_cells rsegs m a [C1 b].
Proof.
  intros m a b BA HM. pose proof (bytes_mapped_rw m a [b] BA HM) as H.
  destruct H as [[_ B] W]. split; [split; [exact (conj I I)| exact B]| exact W].
Qed.

(* [comment removed for export] *)
Lemma rw_cells_bytes : forall m a cs, rw_cells rsegs m a cs -> bytes_at rsegs m a (cells_bytes cs).
Proof. intros m a cs [[_ B] _]. exact B. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_tl : forall m A c cs, rw_cells rsegs m A (c :: cs) -> rw_cells rsegs m (A + Z.of_nat (csize c)) cs.
Proof.
  intros m A c cs [[[WF1 WF2] BA] (W0 & W1 & W2)].
  cbn [cells_bytes] in BA. apply bytes_at_app in BA. destruct BA as [BA1 BA2].
  rewrite (cbytes_length c WF1) in BA2.
  cbn [cells_size] in W1, W2.
  split; [split; [exact WF2| exact BA2]|].
  split; [lia|]. split; [rewrite Nat2Z.inj_add in W1; lia|].
  intros i Hi. replace (A + Z.of_nat (csize c) + i) with (A + (Z.of_nat (csize c) + i)) by lia. apply W2.
  rewrite Nat2Z.inj_add. lia.
Qed.
Lemma rw_cells_hd : forall m A c cs, rw_cells rsegs m A (c :: cs) -> bytes_at rsegs m A (cbytes c).
Proof.
  intros m A c cs [[[WF1 WF2] BA] _]. cbn [cells_bytes] in BA. apply bytes_at_app in BA. tauto.
Qed.
Lemma le8_zero_repeat : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma Z_to_bv8_eq : forall x y, x mod 256 = y mod 256 -> Z_to_bv 8 x = Z_to_bv 8 y.
Proof. intros x y E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. exact E. Qed.

Lemma hdr_word_bytes : forall st b1 h, 0 <= st < 256 -> 0 <= b1 < 256 -> 0 <= h < 2^16 ->
  le4 (Z_to_bv 64 (st + 256 * b1 + 65536 * h)) = [Z_to_bv 8 st; Z_to_bv 8 b1] ++ le2 (Z_to_bv 64 h).
Proof.
  intros st b1 h Hs Hb Hh. unfold le4, le2. rewrite !unsigned_lit by lia.
  cbn [Z_to_le_bytes app]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ].
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ (8 + 8 + 8)) with 16777216. change (2 ^ (8 + 8)) with 65536. change (2 ^ 8) with 256.
  change (2 ^ 16) with 65536 in Hh.
  assert (E1 : (st + 256 * b1 + 65536 * h) / 256 = b1 + 256 * h).
  { replace (st + 256 * b1 + 65536 * h) with ((b1 + 256 * h) * 256 + st) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (E2 : (st + 256 * b1 + 65536 * h) / 65536 = h).
  { replace (st + 256 * b1 + 65536 * h) with (h * 65536 + (st + 256 * b1)) by lia. rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  assert (E3 : (st + 256 * b1 + 65536 * h) / 16777216 = h / 256).
  { replace 16777216 with (65536 * 256) by lia. rewrite <- Z.div_div by lia. rewrite E2. reflexivity. }
  rewrite E1, E2, E3.
  f_equal. { apply Z_to_bv8_eq. rewrite <- Z.add_mod_idemp_r by lia. replace ((256 * b1 + 65536 * h) mod 256) with 0; [lia|].
             symmetry. apply Z.mod_divide; [lia|]. exists (b1 + 256 * h). lia. }
  f_equal. { apply Z_to_bv8_eq. replace (b1 + 256 * h) with (b1 + h * 256) by lia. rewrite Z.mod_add by lia. reflexivity. }
Qed.

Lemma rw_cells_rebytes : forall m A cs cs', cells_wf cs' -> cells_bytes cs' = cells_bytes cs ->
  rw_cells rsegs m A cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' WF' E [[WF B] W]. split; [split; [exact WF'|]|].
  - rewrite E. exact B.
  - rewrite <- (cells_bytes_length cs' WF'), E, (cells_bytes_length cs WF). exact W.
Qed.

Lemma hdr4_join : forall m A st b1 h rest, 0 <= st < 256 -> 0 <= b1 < 256 -> 0 <= h < 2^16 -> cells_wf rest ->
  rw_cells rsegs m A (C1 (Z_to_bv 8 st) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 h) :: rest) ->
  rw_cells rsegs m A (C4 (Z_to_bv 64 (st + 256 * b1 + 65536 * h)) :: rest).
Proof.
  intros m A st b1 h rest Hs Hb Hh WFr H. eapply rw_cells_rebytes; [| | exact H].
  - cbn. split; [exact I| exact WFr].
  - cbn [cells_bytes cbytes]. rewrite hdr_word_bytes by assumption. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma hdr4_split : forall m A st b1 h rest, 0 <= st < 256 -> 0 <= b1 < 256 -> 0 <= h < 2^16 -> cells_wf rest ->
  rw_cells rsegs m A (C4 (Z_to_bv 64 (st + 256 * b1 + 65536 * h)) :: rest) ->
  rw_cells rsegs m A (C1 (Z_to_bv 8 st) :: C1 (Z_to_bv 8 b1) :: C2 (Z_to_bv 64 h) :: rest).
Proof.
  intros m A st b1 h rest Hs Hb Hh WFr H. eapply rw_cells_rebytes; [| | exact H].
  - cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try exact I. exact WFr.
  - cbn [cells_bytes cbytes]. rewrite hdr_word_bytes by assumption. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma land_m4 : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof.
  intros x Hx H4. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.lt_ge_cases i 2) as [L|G].
  - (* [comment removed for export] *)
    assert (Z.testbit x i = false) as ->.
    { rewrite <- (Z.mod_pow2_bits_low x 2 i) by lia. change (2 ^ 2) with 4. rewrite H4. apply Z.bits_0. }
    reflexivity.
  - destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace (Z.testbit 18446744073709551612 i) with true; [apply Bool.andb_true_r|].
      symmetry. change 18446744073709551612 with (Z.ldiff (Z.ones 64) 3). rewrite Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
      rewrite (testbit_high_false 3 2) by lia. rewrite Bool.andb_true_r. apply Z.ltb_lt. lia.
    + rewrite (testbit_high_false x 64) by lia. reflexivity.
Qed.
Lemma shl3_mod32 : forall x, x mod 4 = 0 -> (Z.shiftl x 3 mod 18446744073709551616) mod 32 = 0.
Proof.
  intros x H4. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  set (k := x / 4). assert (X : x = 4 * k) by (subst k; rewrite (Z_div_mod_eq_full x 4) at 1; lia). rewrite X.
  set (y := 4 * k * 8). set (q := y / 18446744073709551616).
  assert (E : y mod 18446744073709551616 = 32 * (k - 576460752303423488 * q)).
  { pose proof (Z_div_mod_eq_full y 18446744073709551616). subst y q. lia. }
  rewrite E, Z.mul_comm. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma land255_low : forall st w, 0 <= st < 256 -> 0 <= w -> Z.land (st + 256 * w) 255 = st.
Proof.
  intros st w Hs Hw. replace 255 with (255 + 256 * 0) by lia. rewrite land_split by lia.
  rewrite Z.land_0_r. change 255 with (Z.ones 8). rewrite Z.land_ones, Z.mod_small by lia. lia.
Qed.
Lemma lxor_lt_256 : forall x x', 0 <= x < 256 -> 0 <= x' < 256 -> 0 <= Z.lxor x x' < 256.
Proof.
  intros x x' Hx Hx'. split; [apply Z.lxor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lxor x x') 0) as [->|NZ]; [lia|].
  apply (proj2 (Z.log2_lt_pow2 (Z.lxor x x') 8 ltac:(pose proof (Z.lxor_nonneg x x'); lia))).
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  apply Z.max_lub_lt.
  - destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - destruct (Z.eq_dec x' 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lxor_split : forall x y x' y', 0 <= x < 256 -> 0 <= x' < 256 ->
  Z.lxor (x + 256 * y) (x' + 256 * y') = Z.lxor x x' + 256 * Z.lxor y y'.
Proof.
  intros x y x' y' Hx Hx'.
  pose proof (lxor_lt_256 x x' Hx Hx') as Hl.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, !testbit_split by lia.
  destruct (i <? 8); rewrite Z.lxor_spec; reflexivity.
Qed.
Lemma cas_set_low : forall st st' w, 0 <= st < 256 -> 0 <= st' < 256 -> 0 <= w ->
  Z.lxor (st + 256 * w) (Z.land (Z.lxor (st + 256 * w) st') 255) = st' + 256 * w.
Proof.
  intros st st' w Hs Hs' Hw.
  pose proof (lxor_lt_256 st st' Hs Hs') as Hl.
  replace st' with (st' + 256 * 0) at 1 by lia. rewrite lxor_split by lia. rewrite Z.lxor_0_r.
  rewrite land255_low by lia.
  replace (Z.lxor st st') with (Z.lxor st st' + 256 * 0) by lia. rewrite lxor_split by lia.
  rewrite Z.lxor_0_r. rewrite <- Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_l. reflexivity.
Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ACells.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARtStmts.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_wg1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_pkh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.
Local Open Scope Z_scope.
Lemma depot_repL_munch : forall L D n0 f0 m m' slo shi,
  depot_repL L rsegs D n0 f0 m -> munch [(slo, shi)] m m' ->
  al_depot_nodes_map1 L + 8 * kDepotNodesL1 <= slo -> n0 + kDepotNodesBlock <= slo -> f0 + kStackStoreBlockBytes <= slo ->
  0 <= al_stackStore L -> 0 <= n0 -> 0 <= f0 -> slo <= shi <= 2^64 ->
  depot_repL L rsegs D n0 f0 m'.
Proof.
  intros L D n0 f0 m m' slo shi REP MU B1 B2 B3 P1 P2 P3 P4.
  eapply depot_repL_agree; [exact REP|]. intros a FA. apply MU. cbn.
  unfold depot_foot, kDepotNodesL1, kDepotNodesBlock, kStackStoreBlockBytes in *. rewrite unsigned_lit by lia. lia.
Qed.

Lemma depot_putC_id_range : forall D k, 1 <= snd (depot_putC D k) <= Z.of_nat (length D) + 1.
Proof.
  intros D k. unfold depot_putC. pose proof (depot_findC_spec D (depot_hashC k) 1) as FS.
  destruct (depot_findC D (depot_hashC k) 1) as [j|]; cbn [snd]; lia.
Qed.

Lemma depot_repL_munchW : forall L D n0 f0 m m' W,
  depot_repL L rsegs D n0 f0 m -> munch W m m' ->
  (forall a, depot_foot L n0 f0 a -> 0 <= a < 2^64 /\ outside W a) ->
  depot_repL L rsegs D n0 f0 m'.
Proof.
  intros L D n0 f0 m m' W REP MU OUT.
  eapply depot_repL_agree; [exact REP|]. intros a FA. destruct (OUT a FA) as [R O]. apply MU.
  rewrite unsigned_lit by lia. exact O.
Qed.

(* [comment removed for export] *)
Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  change 8 with (2 ^ 3) at 1. rewrite Z.mul_comm.
  destruct (Z.lt_ge_cases i 3) as [L|G].
  - rewrite Z.mul_pow2_bits_low by lia.
    replace (Z.testbit 18446744073709551608 i) with false; [apply Bool.andb_false_r|].
    symmetry. change 18446744073709551608 with (Z.ldiff (Z.ones 64) 7). rewrite Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
    replace (Z.testbit 7 i) with true; [cbn [negb]; apply Bool.andb_false_r|]. symmetry. change 7 with (Z.ones 3). rewrite Z.testbit_ones_nonneg by lia. apply Z.ltb_lt. lia.
  - change (x / 8) with (x / 2 ^ 3). rewrite Z.mul_pow2_bits, Z.div_pow2_bits by lia. replace (i - 3 + 3) with i by lia.
    destruct (Z.lt_ge_cases i 64) as [L2|G2].
    + replace (Z.testbit 18446744073709551608 i) with true; [apply Bool.andb_true_r|].
      symmetry. change 18446744073709551608 with (Z.ldiff (Z.ones 64) 7). rewrite Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
      rewrite (testbit_high_false 7 3) by lia. rewrite Bool.andb_true_r. apply Z.ltb_lt. lia.
    + rewrite (testbit_high_false x 64) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma le8_small_split : forall v, 0 <= v < 2^32 -> le8 (Z_to_bv 64 v) = le4 (Z_to_bv 64 v) ++ le4 (Z_to_bv 64 0).
Proof.
  intros v Hv. rewrite <- store_bytes_8'. unfold le4. rewrite !unsigned_lit by lia.
  change 8%nat with (4 + 4)%nat. rewrite OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_pkh.Z_to_le_bytes_add. f_equal.
  cbn [Z.of_nat Z.mul Pos.of_succ_nat Pos.mul]. rewrite Z.shiftr_div_pow2, Z.div_small by lia. reflexivity.
Qed.
Lemma rw_cells_C8_44x : forall m A pre v rest, rw_cells rsegs m A (pre ++ C8 (Z_to_bv 64 v) :: rest) -> 0 <= v < 2^32 ->
  rw_cells rsegs m A (pre ++ C4 (Z_to_bv 64 v) :: C4 (Z_to_bv 64 0) :: rest).
Proof.
  intros m A pre v rest H Hv. eapply rw_cells_rebytes; [| | exact H].
  - destruct H as [[WF _] _]. apply cells_wf_app in WF. apply cells_wf_app. cbn in *. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le8_small_split by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rw_cells_ro : forall m A cs, rw_cells rsegs m A cs -> ro_cells rsegs m A cs.
Proof. intros m A cs [H _]. exact H. Qed.
Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Lemma cas_set_byte1 : forall hi b b', 0 <= b < 256 -> 0 <= b' < 256 -> 0 <= hi ->
  Z.lxor (256 * b + 65536 * hi) (Z.land (Z.lxor (256 * b + 65536 * hi) (256 * b')) 65280) = 256 * b' + 65536 * hi.
Proof.
  intros hi b b' Hb Hb' Hh.
  pose proof (cas_set_low b b' hi Hb Hb' Hh) as E.
  apply (f_equal (fun z => Z.shiftl z 8)) in E.
  rewrite !Z.shiftl_lxor, !Z.shiftl_land, !Z.shiftl_lxor in E.
  rewrite !Z.shiftl_mul_pow2 in E by lia. change (2 ^ 8) with 256 in E.
  replace ((b + 256 * hi) * 256) with (256 * b + 65536 * hi) in E by lia.
  replace ((b' + 256 * hi) * 256) with (256 * b' + 65536 * hi) in E by lia.
  replace (b' * 256) with (256 * b') in E by lia. replace (255 * 256) with 65280 in E by lia. exact E.
Qed.

(* [comment removed for export] *)
Lemma srlw8_byte : forall x, 0 <= x < 2^31 ->
  Z.land (bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 8) mod 18446744073709551616) 255 = (x / 256) mod 256.
Proof.
  intros x Hx. rewrite (bv_wrap_small 32 x) by (unfold bv_modulus; lia).
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  assert (R : 0 <= x / 256 < 2^23) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold bv_swrap, bv_half_modulus. change (bv_modulus 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  rewrite bv_wrap_small by (change (bv_modulus 32) with 4294967296; lia).
  rewrite Z.add_simpl_r, Z.mod_small by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma zeros_split16 : forall m A n, 16 <= n ->
  rw_cells rsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  rw_cells rsegs m A [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB (Z.to_nat (n - 16)) (repeat (Z_to_bv 8 0) (Z.to_nat (n - 16)))].
Proof.
  intros m A n Hn H. eapply rw_cells_rebytes; [| | exact H].
  - cbn. rewrite repeat_length. tauto.
  - cbn [cells_bytes cbytes]. rewrite !le8_zero_repeat, !app_nil_r, <- !repeat_app. f_equal. lia.
Qed.

Lemma cas_set_low0 : forall st' w, 0 <= st' < 256 -> 0 <= w ->
  Z.lxor (256 * w) (Z.land (Z.lxor (256 * w) st') 255) = st' + 256 * w.
Proof. intros st' w H1 H2. pose proof (cas_set_low 0 st' w ltac:(lia) H1 H2) as E. rewrite Z.add_0_l in E. exact E. Qed.
Lemma land255_low0 : forall w, 0 <= w -> Z.land (256 * w) 255 = 0.
Proof. intros w Hw. pose proof (land255_low 0 w ltac:(lia) Hw) as E. rewrite Z.add_0_l in E. exact E. Qed.
