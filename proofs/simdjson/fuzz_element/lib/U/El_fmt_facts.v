(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad PrintfModel PrintfFormats Stdio.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Printf_mlib Printf_pieces.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition FMT_lu : list Z := [37; 108; 117; 0].
Definition FMT_ld : list Z := [37; 108; 100; 0].
Definition FMT_lx : list Z := [37; 108; 120; 0].

Lemma pass1_ok_lu : pass1_ok FMT_lu = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_ld : pass1_ok FMT_ld = true. Proof. vm_compute. reflexivity. Qed.
Lemma pass1_ok_lx : pass1_ok FMT_lx = true. Proof. vm_compute. reflexivity. Qed.
Lemma fp_calls_lu : forall u, fp_calls (Datatypes.length FMT_lu) FMT_lu [PA_z u] = []. Proof. intros; vm_compute; reflexivity. Qed.
Lemma fp_calls_ld : forall i, fp_calls (Datatypes.length FMT_ld) FMT_ld [PA_l i] = []. Proof. intros; vm_compute; reflexivity. Qed.
Lemma fp_calls_lx : forall u, fp_calls (Datatypes.length FMT_lx) FMT_lx [PA_z u] = []. Proof. intros; vm_compute; reflexivity. Qed.

Lemma hex_digits_zlength : forall l x, 0 <= zlength (hex_digits l x) <= 16.
Proof.
  intros l x. unfold zlength, hex_digits. pose proof (digits_aux_length 16 16 (fun v => Z.lor (znth XDIGITS v) l) x []) as L.
  cbn [Datatypes.length Nat.add] in L. lia.
Qed.
Lemma hex_digits_0' : forall l, hex_digits l 0 = [].
Proof. intros. reflexivity. Qed.
Lemma hex_digits_nz : forall l x, 1 <= x < 2^64 -> hex_digits l x <> [].
Proof.
  intros l x Hx. unfold hex_digits. rewrite digits_aux_S. replace (x =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite digits_aux_acc. intros E. apply app_eq_nil in E. destruct E as [_ E]. discriminate E.
Qed.

Definition upieces (u : Z) : list (list Z) := if u =? 0 then [[]; [48]; []] else [[]; dec_digits u].
Definition ulen (u : Z) : Z := if u =? 0 then 1 else zlength (dec_digits u).
Definition xpieces (u : Z) : list (list Z) := if u =? 0 then [[]; [48]; []] else [[]; hex_digits 32 u].
Definition xlen (u : Z) : Z := if u =? 0 then 1 else zlength (hex_digits 32 u).
Definition labs (i : Z) : Z := if i <? 0 then - i else i.
Definition lpieces (i : Z) : list (list Z) :=
  if i =? 0 then [[]; [48]; []] else [(if i <? 0 then [45] else []); dec_digits (labs i)].
Definition llen (i : Z) : Z := if i =? 0 then 1 else (if i <? 0 then 1 else 0) + zlength (dec_digits (labs i)).

Lemma ulen_bound : forall u, 1 <= ulen u <= 20.
Proof.
  intros u. unfold ulen. pose proof (dec_digits_zlength u). destruct (Z.eqb_spec u 0); [lia|].
  assert (1 <= zlength (dec_digits u)); [|lia].
  destruct (Z_lt_dec u 1).
  {
    unfold dec_digits. rewrite digits_aux_S. destruct (u =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
    rewrite digits_aux_acc. unfold zlength. rewrite app_length. cbn [Datatypes.length Nat.add]. lia. }
  destruct (Z_lt_dec u (2^64)).
  - pose proof (dec_digits_nz u ltac:(lia)). destruct (dec_digits u); [contradiction | unfold zlength; cbn; lia].
  - unfold dec_digits. rewrite digits_aux_S. destruct (u =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
    rewrite digits_aux_acc. unfold zlength. rewrite app_length. cbn [Datatypes.length Nat.add]. lia.
Qed.
Lemma xlen_bound : forall u, 1 <= xlen u <= 16.
Proof.
  intros u. unfold xlen. pose proof (hex_digits_zlength 32 u). destruct (Z.eqb_spec u 0); [lia|].
  assert (1 <= zlength (hex_digits 32 u)); [|lia].
  unfold hex_digits. rewrite digits_aux_S. destruct (u =? 0) eqn:E; [apply Z.eqb_eq in E; lia|].
  rewrite digits_aux_acc. unfold zlength. rewrite app_length. cbn [Datatypes.length Nat.add]. lia.
Qed.
Lemma concat_upieces : forall u, zlength (concat (upieces u)) = ulen u.
Proof. intros u. unfold upieces, ulen. destruct (u =? 0); cbn [concat app]; rewrite ?app_nil_r; [reflexivity | reflexivity]. Qed.
Lemma concat_xpieces : forall u, zlength (concat (xpieces u)) = xlen u.
Proof. intros u. unfold xpieces, xlen. destruct (u =? 0); cbn [concat app]; rewrite ?app_nil_r; [reflexivity | reflexivity]. Qed.

Definition DIR_l (t ty : Z) : dir := {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := t; d_ty := ty; d_star := false |}.

Lemma conv_pieces_lu : forall cnt u, 0 <= cnt -> 0 <= u < 2^64 -> cnt + 21 <= INT_MAX ->
  conv_pieces cnt (DIR_l 117 T_ULONG) (PA_z u) = Some (upieces u, cnt + ulen u).
Proof.
  intros cnt u Hc Hu HI. pose proof (dec_digits_zlength u) as DL. unfold upieces, ulen.
  destruct (Z.eqb_spec u 0) as [->|NZ].
  - unfold conv_pieces, DIR_l. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.eqb Z.land LEFT_ADJ negb T_SIZET T_ULONG Pos.eqb andb orb Z.ltb Z.compare].
    unfold int_pieces. cbn [andb Z.eqb]. rewrite dec_digits_0. change (zlength (@nil Z)) with 0.
    change (Z.max (-1) (0 + 1)) with 1. apply tail_pieces_zero1; lia.
  - unfold conv_pieces, DIR_l. cbn [d_fl d_w d_p d_xp d_t d_ty]. cbv beta iota zeta delta [Z.land LEFT_ADJ negb T_SIZET T_ULONG Pos.eqb andb orb Z.ltb Z.compare].
    change (T_ULONG =? T_ULONG) with true. change (14 =? 4)%Z with false. change (117 =? 117) with true. cbn [negb andb orb]. cbv beta iota.
    unfold int_pieces. cbn [andb].
    replace (u =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
    pose proof (dec_digits_nz u ltac:(lia)) as NE.
    assert (L1 : 1 <= zlength (dec_digits u)) by (destruct (dec_digits u); [contradiction | unfold zlength; cbn; lia]).
    rewrite Z.add_0_r. cbv beta iota.
    rewrite tail_pieces_plain by lia. reflexivity.
Qed.

Lemma conv_pieces_lx : forall cnt u, 0 <= cnt -> 0 <= u < 2^64 -> cnt + 17 <= INT_MAX ->
  conv_pieces cnt (DIR_l 120 T_ULONG) (PA_z u) = Some (xpieces u, cnt + xlen u).
Proof.
  intros cnt u Hc Hu HI. pose proof (hex_digits_zlength 32 u) as DL. unfold xpieces, xlen.
  unfold conv_pieces, DIR_l, int_pieces. remember (u =? 0) as b eqn:Hb.
  cbn -[hex_digits dec_digits tail_pieces zlength Z.max Z.add].
  replace (if Z.land 0 LEFT_ADJ =? 0 then 0 else Z.land 0 (Z.lnot ZERO_PAD)) with 0 by reflexivity.
  replace (Z.land 0 ALT_FORM =? 0) with true by reflexivity.
  destruct (Z.eqb_spec u 0) as [->|NZ]; subst b; cbn -[hex_digits dec_digits tail_pieces zlength Z.max Z.add].
  - change ((-1) `max` (zlength (@nil Z) + 1)) with 1. apply tail_pieces_zero1; lia.
  - pose proof (hex_digits_nz 32 u ltac:(lia)) as NE.
    assert (L1 : 1 <= zlength (hex_digits 32 u)) by (destruct (hex_digits 32 u); [contradiction | unfold zlength; cbn; lia]).
    change (Z.land 120 32) with 32. rewrite Z.add_0_r. rewrite tail_pieces_plain by lia. reflexivity.
Qed.

Lemma labs_range : forall i, -2^63 <= i < 2^63 -> 0 <= labs i <= 2^63.
Proof. intros i Hi. unfold labs. destruct (Z.ltb_spec i 0); lia. Qed.

Lemma tail_pieces_minus : forall cnt p body, 0 <= cnt -> 1 <= zlength body -> p <= zlength body -> cnt + 1 + zlength body <= INT_MAX ->
  tail_pieces cnt 0 0 p [45] body = Some ([[45]; body], cnt + (1 + zlength body)).
Proof.
  intros cnt p body Hc Hb Hp HI. unfold tail_pieces. cbv zeta. change (zlength [45]) with 1.
  replace (Z.max p (zlength body)) with (zlength body) by lia.
  replace (INT_MAX - 1 <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.max 0 (1 + zlength body)) with (1 + zlength body) by lia.
  replace (INT_MAX - cnt <? 1 + zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces.
  replace (1 + zlength body <=? 1 + zlength body) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ]. reflexivity.
Qed.

Lemma conv_pieces_ld : forall cnt i, 0 <= cnt -> -2^63 <= i < 2^63 -> cnt + 22 <= INT_MAX ->
  conv_pieces cnt (DIR_l 100 T_LONG) (PA_l i) = Some (lpieces i, cnt + llen i).
Proof.
  intros cnt i Hc Hi HI. pose proof (labs_range i Hi) as LA. pose proof (dec_digits_zlength (labs i)) as DL. unfold lpieces, llen.
  unfold conv_pieces, DIR_l. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota. change (negb (T_LONG =? T_LONG)) with false. cbv iota.
  change (negb (Z.land 0 MARK_POS =? 0)) with false. change (negb (Z.land 0 PAD_POS =? 0)) with false. cbv iota.
  destruct (Z.ltb_spec i 0) as [NEG|NNEG].
  - replace (i mod 2^64) with (i + 2^64) by (apply Z.mod_unique with (q := -1); lia).
    replace (INTMAX_MAX <? i + 2^64) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia).
    replace (- (i + 2^64) mod 2^64)%Z with (labs i) by (unfold labs; replace (i <? 0) with true by (symmetry; apply Z.ltb_lt; lia); apply Z.mod_unique with (q := -1); lia).
    replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    unfold int_pieces. cbn [andb].
    replace (labs i =? 0) with false by (symmetry; apply Z.eqb_neq; unfold labs; destruct (Z.ltb_spec i 0); lia).
    pose proof (dec_digits_nz (labs i) ltac:(unfold labs in *; destruct (Z.ltb_spec i 0); lia)) as NE.
    assert (L1 : 1 <= zlength (dec_digits (labs i))) by (destruct (dec_digits (labs i)); [contradiction | unfold zlength; cbn; lia]).
    cbn [andb]. rewrite Z.add_0_r. rewrite tail_pieces_minus by lia. reflexivity.
  - replace (i mod 2^64) with i by (symmetry; apply Z.mod_small; lia).
    replace (INTMAX_MAX <? i) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia).
    unfold int_pieces. cbn [andb].
    replace (labs i) with i in * by (unfold labs; replace (i <? 0) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
    destruct (Z.eqb_spec i 0) as [->|NZ].
    + rewrite dec_digits_0. change (zlength (@nil Z)) with 0. change (Z.max (-1) (0 + 1)) with 1. cbn [Z.add]. apply tail_pieces_zero1; lia.
    + pose proof (dec_digits_nz i ltac:(lia)) as NE.
      assert (L1 : 1 <= zlength (dec_digits i)) by (destruct (dec_digits i); [contradiction | unfold zlength; cbn; lia]).
      cbn [andb]. rewrite Z.add_0_r. cbn [Z.add]. rewrite tail_pieces_plain by lia. reflexivity.
Qed.

Lemma ppl_end : forall fuel args cnt, printf_pieces_loop (S fuel) [0] args cnt = Some ([], cnt).
Proof. intros. reflexivity. Qed.

Lemma printf_pieces_lu : forall u, 0 <= u < 2^64 -> printf_pieces FMT_lu [PA_z u] = Some ([] :: upieces u, ulen u).
Proof.
  intros u Hu. unfold printf_pieces. change (Datatypes.length FMT_lu) with 4%nat.
  ppl_step. change (dir_args _ [PA_z u]) with (Some (DIR_l 117 T_ULONG, [PA_z u])). cbv beta iota.
  rewrite conv_pieces_lu by (unfold INT_MAX; lia). cbv beta iota. rewrite ppl_end.
  unfold upieces, ulen. destruct (u =? 0); cbv beta iota; repeat f_equal; lia.
Qed.
Lemma printf_pieces_lx : forall u, 0 <= u < 2^64 -> printf_pieces FMT_lx [PA_z u] = Some ([] :: xpieces u, xlen u).
Proof.
  intros u Hu. unfold printf_pieces. change (Datatypes.length FMT_lx) with 4%nat.
  ppl_step. change (dir_args _ [PA_z u]) with (Some (DIR_l 120 T_ULONG, [PA_z u])). cbv beta iota.
  rewrite conv_pieces_lx by (unfold INT_MAX; lia). cbv beta iota. rewrite ppl_end.
  unfold xpieces, xlen. destruct (u =? 0); cbv beta iota; repeat f_equal; lia.
Qed.
Lemma printf_pieces_ld : forall i, -2^63 <= i < 2^63 -> printf_pieces FMT_ld [PA_l i] = Some ([] :: lpieces i, llen i).
Proof.
  intros i Hi. unfold printf_pieces. change (Datatypes.length FMT_ld) with 4%nat.
  ppl_step. change (dir_args _ [PA_l i]) with (Some (DIR_l 100 T_LONG, [PA_l i])). cbv beta iota.
  rewrite conv_pieces_ld by (unfold INT_MAX; lia). cbv beta iota. rewrite ppl_end.
  unfold lpieces, llen. destruct (i =? 0); cbv beta iota; repeat f_equal; lia.
Qed.
