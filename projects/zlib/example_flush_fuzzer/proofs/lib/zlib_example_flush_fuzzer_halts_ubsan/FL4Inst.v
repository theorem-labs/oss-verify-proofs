(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import ExFlushIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  Prog ZIface DeflateState Deflate InflateState Inflate InflateSync HarnessKit HarnessFacts HarnessSmallStages HarnessSmallFacts HarnessFlush HarnessFlushFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec Require Import FlushStages.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition zpad (k : Z) (l : list Z) : list Z := firstn (Z.to_nat k) (l ++ repeat 0 (Z.to_nat k)).
Lemma zpad_length : forall k l, 0 <= k -> Z.of_nat (length (zpad k l)) = k.
Proof. intros k l Hk. unfold zpad. rewrite length_firstn, length_app, repeat_length. rewrite Nat.min_l by lia. lia. Qed.
Lemma zpad_id : forall k l, Z.of_nat (length l) = k -> zpad k l = l.
Proof. intros k l E. unfold zpad. replace (Z.to_nat k) with (length l) by lia. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Definition bnorm (l : list Z) : list Z := map (fun z => z mod 256) l.
Lemma bnorm_id : forall l, Forall (fun b => 0 <= b < 256) l -> bnorm l = l.
Proof. intros l H. unfold bnorm. induction H as [|x l Hx H IH]; [reflexivity|]. cbn. rewrite Z.mod_small by lia. f_equal. exact IH. Qed.
Definition carr (c : list Z) : arr := arr_of_list (bnorm c).

Definition inzb (x : Z) (l : list Z) : bool := existsb (Z.eqb x) l.
Lemma inzb_In : forall x l, inzb x l = true -> In x l.
Proof. intros x l. unfold inzb. induction l as [|y l IH]; cbn; [discriminate|]. destruct (Z.eqb_spec x y) as [->|NE]; cbn; [left; reflexivity | intros H; right; exact (IH H)]. Qed.
Lemma In_inzb : forall x l, In x l -> inzb x l = true.
Proof. intros x l. unfold inzb. induction l as [|y l IH]; cbn; [intros []|]. intros [->|H]; [rewrite Z.eqb_refl; reflexivity|]. rewrite (IH H). apply Bool.orb_true_r. Qed.

Definition fl4_compr (d : list Z) : list Z := zpad (CLEN (zlength d)) (arr_to_list (fl_compr2 d)).
Definition fl4_busy (d : list Z) : bool := fl_busy d.
Definition fl4_tot (d : list Z) : Z := Z.max 2 (Z.min (fl_tot d) (CLEN (zlength d))).

Definition fl4_i1 (c : list Z) (n : Z) : i1exit :=
  let rc := zr_rc (fl_ir1 (carr c) n) in
  if rc =? 0 then I1_OK else if inzb rc INFL_ERRS then I1_E rc else I1_E ZE_DATA_ERROR.
Definition fl4_is (c : list Z) (clen n : Z) : isexit :=
  let rc := zr_rc (fl_ir2 (carr c) clen n) in
  if rc =? 0 then IS_OK else if inzb rc SYNC_ERRS then IS_E rc else IS_E ZE_DATA_ERROR.
Definition fl4_rc3 (c : list Z) (clen n : Z) : Z :=
  let rc := zr_rc (fl_ir3 (carr c) clen n) in if inzb rc INFL_RCS then rc else ZE_DATA_ERROR.
Definition fl4_i2 (c : list Z) (clen n : Z) : i2exit :=
  match fl_iasked3 (carr c) clen n with Some _ => I2_W | None => I2_R (fl4_rc3 c clen n) end.
Definition fl4_i2b (c : list Z) (clen n : Z) : Z := fl4_rc3 c clen n.

Lemma CLEN_nonneg : forall n, 0 <= n -> 0 <= CLEN n.
Proof. intros n Hn. pose proof (CLEN_ge n Hn). lia. Qed.

Lemma fl4_compr_len : forall d, Z.of_nat (length (fl4_compr d)) = CLEN (Z.of_nat (length d)).
Proof. intros d. unfold fl4_compr, zlength. apply zpad_length. apply CLEN_nonneg. lia. Qed.
Lemma fl4_tot_range : forall d, 2 <= fl4_tot d <= CLEN (Z.of_nat (length d)).
Proof. intros d. unfold fl4_tot, zlength. pose proof (CLEN_ge (Z.of_nat (length d)) ltac:(lia)). lia. Qed.
Lemma fl4_i1_errs : forall c n e, fl4_i1 c n = I1_E e -> In e INFL_ERRS.
Proof.
  intros c n e. unfold fl4_i1. cbv zeta. destruct (zr_rc (fl_ir1 (carr c) n) =? 0); [discriminate|].
  destruct (inzb (zr_rc (fl_ir1 (carr c) n)) INFL_ERRS) eqn:B; intros X; injection X as <-; [apply inzb_In; exact B | cbn; tauto].
Qed.
Lemma fl4_is_errs : forall c clen n e, fl4_is c clen n = IS_E e -> In e SYNC_ERRS.
Proof.
  intros c clen n e. unfold fl4_is. cbv zeta. destruct (zr_rc (fl_ir2 (carr c) clen n) =? 0); [discriminate|].
  destruct (inzb (zr_rc (fl_ir2 (carr c) clen n)) SYNC_ERRS) eqn:B; intros X; injection X as <-; [apply inzb_In; exact B | cbn; tauto].
Qed.
Lemma fl4_rc3_rcs : forall c clen n, In (fl4_rc3 c clen n) INFL_RCS.
Proof.
  intros c clen n. unfold fl4_rc3. cbv zeta. destruct (inzb (zr_rc (fl_ir3 (carr c) clen n)) INFL_RCS) eqn:B; [apply inzb_In; exact B | cbn; tauto].
Qed.
Lemma fl4_i2_rcs : forall c clen n rc, fl4_i2 c clen n = I2_R rc -> In rc INFL_RCS.
Proof. intros c clen n rc. unfold fl4_i2. destruct (fl_iasked3 (carr c) clen n); [discriminate|]. intros X; injection X as <-. apply fl4_rc3_rcs. Qed.
Lemma fl4_i2b_rcs : forall c clen n, In (fl4_i2b c clen n) INFL_RCS.
Proof. intros. unfold fl4_i2b. apply fl4_rc3_rcs. Qed.

Definition FL4 : flush_model :=
  FLUSH_MODEL fl4_compr fl4_busy fl4_tot fl4_i1 fl4_is fl4_i2 fl4_i2b
              fl4_compr_len fl4_tot_range fl4_i1_errs fl4_is_errs fl4_i2_rcs fl4_i2b_rcs.

Lemma fl4_busy_eq : forall d, fm_busy FL4 d = fl_busy d.
Proof. reflexivity. Qed.

Lemma fl4_tot_eq : forall d, 2 <= fl_tot d <= CLEN (zlength d) -> fm_tot FL4 d = fl_tot d.
Proof. intros d H. cbn [fm_tot FL4]. unfold fl4_tot. lia. Qed.


Lemma fl4_compr_eq : forall d, Z.of_nat (length (arr_to_list (fl_compr2 d))) = CLEN (zlength d) ->
  fm_compr FL4 d = arr_to_list (fl_compr2 d).
Proof. intros d H. cbn [fm_compr FL4]. unfold fl4_compr. apply zpad_id. exact H. Qed.

Lemma fl4_i1_eq : forall c n, let rc := zr_rc (fl_ir1 (carr c) n) in
  (rc = 0 \/ In rc INFL_ERRS) -> fm_i1 FL4 c n = (if rc =? 0 then I1_OK else I1_E rc).
Proof.
  intros c n. cbv zeta. intros H. cbn [fm_i1 FL4]. unfold fl4_i1. cbv zeta.
  destruct (Z.eqb_spec (zr_rc (fl_ir1 (carr c) n)) 0) as [E|NE]; [reflexivity|].
  destruct H as [H|H]; [exfalso; exact (NE H)|]. rewrite (In_inzb _ _ H). reflexivity.
Qed.

Lemma fl4_is_eq : forall c clen n, let rc := zr_rc (fl_ir2 (carr c) clen n) in
  (rc = 0 \/ In rc SYNC_ERRS) -> fm_is FL4 c clen n = (if rc =? 0 then IS_OK else IS_E rc).
Proof.
  intros c clen n. cbv zeta. intros H. cbn [fm_is FL4]. unfold fl4_is. cbv zeta.
  destruct (Z.eqb_spec (zr_rc (fl_ir2 (carr c) clen n)) 0) as [E|NE]; [reflexivity|].
  destruct H as [H|H]; [exfalso; exact (NE H)|]. rewrite (In_inzb _ _ H). reflexivity.
Qed.

Lemma fl4_i2_eq : forall c clen n, In (zr_rc (fl_ir3 (carr c) clen n)) INFL_RCS ->
  fm_i2 FL4 c clen n = match fl_iasked3 (carr c) clen n with Some _ => I2_W | None => I2_R (zr_rc (fl_ir3 (carr c) clen n)) end.
Proof. intros c clen n H. cbn [fm_i2 FL4]. unfold fl4_i2, fl4_rc3. cbv zeta. rewrite (In_inzb _ _ H). reflexivity. Qed.

Lemma fl4_i2b_eq : forall c clen n, In (zr_rc (fl_ir3 (carr c) clen n)) INFL_RCS -> fm_i2b FL4 c clen n = zr_rc (fl_ir3 (carr c) clen n).
Proof. intros c clen n H. cbn [fm_i2b FL4]. unfold fl4_i2b, fl4_rc3. cbv zeta. rewrite (In_inzb _ _ H). reflexivity. Qed.

Lemma carr_bytes : forall c, Forall (fun b => 0 <= b < 256) c -> carr c = arr_of_list c.
Proof. intros c H. unfold carr. rewrite (bnorm_id c H). reflexivity. Qed.
