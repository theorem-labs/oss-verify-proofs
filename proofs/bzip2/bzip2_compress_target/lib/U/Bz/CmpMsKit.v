(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzArrD. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem CmpFsKit. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasMs.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zx16_lit : forall x, 0 <= x < 65536 -> zx16 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof. intros x Hx. unfold zx16. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma zext32_id : forall q, q * 4294967296 / 4294967296 = q.
Proof. intros q. apply Z.div_mul. lia. Qed.
(* [comment removed for export] *)
Lemma zext32_x2 : forall q, q * 4294967296 / 2147483648 = q * 2.
Proof. intros q. replace (q * 4294967296) with ((q * 2) * 2147483648) by lia. apply Z.div_mul. lia. Qed.
Lemma zext32_x4 : forall q, q * 4294967296 / 1073741824 = q * 4.
Proof. intros q. replace (q * 4294967296) with ((q * 4) * 1073741824) by lia. apply Z.div_mul. lia. Qed.
(* [comment removed for export] *)
Lemma zext16_x4 : forall q, 0 <= q -> q * 281474976710656 mod 18446744073709551616 / 70368744177664 = (q mod 65536) * 4.
Proof. intros q Hq. Z.div_mod_to_equations. nia. Qed.
Lemma zext16_id : forall q, 0 <= q -> q * 281474976710656 mod 18446744073709551616 / 281474976710656 = q mod 65536.
Proof. intros q Hq. Z.div_mod_to_equations. nia. Qed.
Lemma zext16_hi : forall q, 0 <= q -> q * 281474976710656 mod 18446744073709551616 / 72057594037927936 = (q mod 65536) / 256.
Proof. intros q Hq. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
Lemma gwrap_sub_flag : forall n i, 0 <= n < 2147483648 -> 0 <= i < 2147483648 ->
  bv_swrap 32 (i - Z.land ((Z.b2z (i <? n) + -1) mod 18446744073709551616) n) = gwrap n i.
Proof.
  intros n i Hn Hi. unfold gwrap. destruct (Z.ltb_spec i n); destruct (Z.leb_spec n i); try lia; cbn [Z.b2z].
  - change ((1 + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.sub_0_r. apply swrap32_small. lia.
  - change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_small by lia. apply swrap32_small. lia.
Qed.

(* [comment removed for export] *)
Lemma bveqb0_true : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = true -> x = 0.
Proof.
  intros x Hx H. unfold bv_eqb in H. apply Z.eqb_eq in H. rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616 in H. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma bvlts0_true : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = true -> x < 0.
Proof.
  intros x Hx H. rewrite bv_lts_zero_r in H. apply Z.leb_le in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616 in H. change (2^63) with 9223372036854775808 in H. Z.div_mod_to_equations. lia.
Qed.
Lemma bvlts0_false : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0) = false -> 0 <= x.
Proof.
  intros x Hx H. rewrite bv_lts_zero_r in H. apply Z.leb_gt in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
  change (bv_modulus 64) with 18446744073709551616 in H. change (2^63) with 9223372036854775808 in H. Z.div_mod_to_equations. lia.
Qed.
Lemma bgez_taken : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0)) = true -> 0 <= x.
Proof. intros x Hx H. apply (bvlts0_false x Hx). destruct (bv_lts _ _); [discriminate| reflexivity]. Qed.
Lemma bgez_not_taken : forall x, - 9223372036854775808 <= x < 9223372036854775808 ->
  negb (bv_lts (Z_to_bv 64 x) (Z_to_bv 64 0)) = false -> x < 0.
Proof. intros x Hx H. apply (bvlts0_true x Hx). destruct (bv_lts _ _); [reflexivity| discriminate]. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record msenv := ME {
  me_ra : word; me_sp : word; me_gp : word; me_tp : word;
  me_s0 : word; me_s1 : word; me_s2 : word; me_s3 : word; me_s4 : word; me_s5 : word;
  me_s6 : word; me_s7 : word; me_s8 : word; me_s9 : word; me_s10 : word; me_s11 : word;
  me_F : bvmap 5 word; me_fc : bv 32;
  me_E : Z; me_A1 : Z; me_A2 : Z; me_FT : Z;     (* [comment removed for export] *)
  me_n : Z; me_qo : Z; me_lo : Z;                (* [comment removed for export] *)
  me_qE : Z; me_q1 : Z; me_q2 : Z; me_qF : Z; me_qsp : Z; me_qq : Z;   (* [comment removed for export] *)
  me_a1 : zarr; me_a2 : zarr; me_ft : zarr;      (* [comment removed for export] *)
  me_sv : word;                                  (* [comment removed for export] *)
  me_m0 : word -> option byte                    (* [comment removed for export] *)
}.

Definition CEILm : Z := alloc_ceiling.  (* [comment removed for export] *)

Definition msenv_ok (X : msenv) : Prop :=
  let usp := bv_unsigned (me_sp X) in
  0 < me_E X /\ me_E X + 55768 <= CEILm /\
  0 < me_A1 X /\ me_A1 X + ARR1_SIZE <= CEILm /\
  0 < me_A2 X /\ me_A2 X + ARR2_SIZE <= CEILm /\
  0 < me_FT X /\ me_FT X + 262148 <= CEILm /\
  CEILm <= me_lo X /\ me_lo X + 8192 <= usp /\ usp < 18446744073709551616 /\
  me_E X = 16 * me_qE X /\ me_A1 X = 16 * me_q1 X /\ me_A2 X = 16 * me_q2 X /\ me_FT X = 16 * me_qF X /\ usp = 16 * me_qsp X /\
  10000 <= me_n X <= (NBLOCKMAX + 19) /\ me_n X + 34 <= me_qo X <= me_n X + 35 /\ me_qo X = 2 * me_qq X /\
  zbok (me_a1 X) /\ zbok (me_a2 X) /\ (forall i, 0 <= zget (me_ft X) i < 4294967296).

Definition apartm (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.   (* [comment removed for export] *)
Definition msenv_sep (X : msenv) : Prop :=
  apartm (me_A1 X) ARR1_SIZE (me_A2 X) ARR2_SIZE /\ apartm (me_A1 X) ARR1_SIZE (me_FT X) 262148 /\
  apartm (me_A2 X) ARR2_SIZE (me_FT X) 262148 /\
  apartm (me_E X) 55768 (me_A1 X) ARR1_SIZE /\ apartm (me_E X) 55768 (me_A2 X) ARR2_SIZE /\ apartm (me_E X) 55768 (me_FT X) 262148.
End ACeilS1.


(* [comment removed for export] *)
Ltac msenv_open XOK :=
  let H := fresh "XL" in
  pose proof XOK as H; unfold msenv_ok, CEILm in H; cbv zeta in H;
  let A1OK := fresh "A1OK" in let A2OK := fresh "A2OK" in let FTOK := fresh "FTOK" in
  cps_destruct H as (?XEl & ?XEh & ?XA1l & ?XA1h & ?XA2l & ?XA2h & ?XFl & ?XFh & ?XLO & ?XLOF & ?XSP & ?ALE & ?AL1 & ?AL2 & ?ALF & ?ALS
              & ?LNB & ?LQO & ?ALQ & A1OK & A2OK & FTOK).
Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma key_div : forall h b, 0 <= h < 256 -> (h + 256 * b) / 256 = b.
Proof. intros. Z.div_mod_to_equations. lia. Qed.
Lemma lor_hb : forall h b, 0 <= h < 256 -> 0 <= b -> Z.lor (b * 256) h = h + 256 * b.
Proof. intros h b Hh Hb. rewrite Z.lor_comm. rewrite lor_mul256 by lia. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor_hb4 : forall h b, 0 <= h < 256 -> 0 <= b -> Z.lor (b * 1024) (h * 4) = (h + 256 * b) * 4.
Proof.
  intros h b Hh Hb. replace (b * 1024) with ((b * 256) * 2 ^ 2) by lia. replace (h * 4) with (h * 2 ^ 2) by lia.
  rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite <- Z.shiftl_lor. rewrite lor_hb by lia. rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land1020_enum : forall t, 0 <= t < 1024 -> Z.land t 1020 = t / 4 * 4.
Proof.
  intros t Ht.
  pose proof (zseq_forallb (fun t => Z.land t 1020 =? t / 4 * 4) 1024 0 ltac:(vm_compute; reflexivity) t ltac:(lia)) as H.
  cbn beta in H. apply Z.eqb_eq in H. exact H.
Qed.
Lemma srl6_and1020 : forall s, 0 <= s < 65536 -> Z.land (s / 64) 1020 = s / 256 * 4.
Proof.
  intros s Hs. rewrite land1020_enum by (Z.div_mod_to_equations; lia).
  replace (s / 256) with (s / 64 / 4) by (rewrite Z.div_div by lia; reflexivity). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sll48_srl46 : forall q, q * 281474976710656 / 70368744177664 = q * 4.
Proof. intros q. replace (q * 281474976710656) with ((q * 4) * 70368744177664) by lia. apply Z.div_mul. lia. Qed.
Lemma sll48_srl48 : forall q, q * 281474976710656 / 281474976710656 = q.
Proof. intros q. apply Z.div_mul. lia. Qed.
Lemma sll48_srl56 : forall q, q * 281474976710656 / 72057594037927936 = q / 256.
Proof.
  intros q. replace 72057594037927936 with (281474976710656 * 256) by reflexivity.
  rewrite <- Z.div_div by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma div3_magic : forall h, 0 <= h < 1024 -> h * 1431655766 / 4294967296 = h / 3.
Proof.
  intros h Hh.
  pose proof (zseq_forallb (fun h => h * 1431655766 / 4294967296 =? h / 3) 1024 0 ltac:(vm_compute; reflexivity) h ltac:(lia)) as H.
  cbn beta in H. apply Z.eqb_eq in H. exact H.
Qed.

End ACeilS2.
