(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface DeflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Record zs_ptrs : Type := ZSP {
  zp_in : Z; zp_out : Z; zp_zalloc : Z; zp_zfree : Z; zp_opaque : Z; zp_reserved : Z;
  zp_msg : Z -> Z }.

Definition zsl_SIZE : Z := 112.

Definition zsl_layout : list (Z * nat) := [
  (0, 8%nat) ;
  (8, 4%nat) ;
  (16, 8%nat) ;
  (24, 8%nat) ;
  (32, 4%nat) ;
  (40, 8%nat) ;
  (48, 8%nat) ;
  (56, 8%nat) ;
  (64, 8%nat) ;
  (72, 8%nat) ;
  (80, 8%nat) ;
  (88, 4%nat) ;
  (96, 8%nat) ;
  (104, 8%nat) ].

Definition zsl_vals (p : zs_ptrs) (S : Z) (st : cstrm) : list Z := [
  zp_in p + cs_next_in st ;
  cs_avail_in st ;
  cs_total_in st ;
  zp_out p + Z.of_nat (length (cs_out_rev st)) ;
  cs_avail_out st ;
  cs_total_out st ;
  zp_msg p (cs_msg st) ;
  S ;
  zp_zalloc p ;
  zp_zfree p ;
  zp_opaque p ;
  cs_data_type st ;
  cs_adler st ;
  zp_reserved p ].

Lemma zsl_layout_within : layout_within zsl_layout zsl_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

Section WithImage.
Variable segs : list Segment.

Definition zsl_scalars (mem : word -> option byte) (strm : Z) (p : zs_ptrs) (S : Z) (st : cstrm) : Prop :=
  fields segs mem strm zsl_layout (zsl_vals p S st).

Definition zsl_input (mem : word -> option byte) (p : zs_ptrs) (st : cstrm) : Prop :=
  cells segs mem (zp_in p) 1 1 (arr_len (cs_input st)) (arr_get (cs_input st)).


Lemma zsl_next_in : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 0) 8 (zp_in p + cs_next_in st).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 0 0 8%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_avail_in : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 8) 4 (cs_avail_in st).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 1 8 4%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_total_in : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 16) 8 (cs_total_in st).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 2 16 8%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_next_out : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 24) 8 (zp_out p + Z.of_nat (length (cs_out_rev st))).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 3 24 8%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_avail_out : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 32) 4 (cs_avail_out st).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 4 32 4%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_total_out : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 40) 8 (cs_total_out st).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 5 40 8%nat _ H eq_refl eq_refl). Qed.


Lemma zsl_state : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 56) 8 (S).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 7 56 8%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_zalloc : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 64) 8 (zp_zalloc p).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 8 64 8%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_zfree : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 72) 8 (zp_zfree p).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 9 72 8%nat _ H eq_refl eq_refl). Qed.


Lemma zsl_data_type : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 88) 4 (cs_data_type st).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 11 88 4%nat _ H eq_refl eq_refl). Qed.

Lemma zsl_adler : forall mem strm p S st, zsl_scalars mem strm p S st -> cell segs mem (strm + 96) 8 (cs_adler st).
Proof. intros mem strm p S st H. exact (fields_nth segs mem strm _ _ 12 96 8%nat _ H eq_refl eq_refl). Qed.



Lemma zsl_upd_next_in : forall mem strm p S st v,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars (wbytes mem (zw (strm + 0)) (Z_to_le_bytes 8 (zp_in p + v))) strm p S (cset_next_in st v).
Proof.
  intros mem strm p S st v H HS0 HS1.
  exact (fields_write_field segs mem strm _ _ zsl_SIZE 0 0 8%nat (zp_in p + v) H eq_refl
           ltac:(vm_compute; reflexivity) zsl_layout_within HS0 HS1).
Qed.

Lemma zsl_upd_avail_in : forall mem strm p S st v,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars (wbytes mem (zw (strm + 8)) (Z_to_le_bytes 4 (v))) strm p S (cset_avail_in st v).
Proof.
  intros mem strm p S st v H HS0 HS1.
  exact (fields_write_field segs mem strm _ _ zsl_SIZE 1 8 4%nat (v) H eq_refl
           ltac:(vm_compute; reflexivity) zsl_layout_within HS0 HS1).
Qed.

Lemma zsl_upd_total_in : forall mem strm p S st v,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars (wbytes mem (zw (strm + 16)) (Z_to_le_bytes 8 (v))) strm p S (cset_total_in st v).
Proof.
  intros mem strm p S st v H HS0 HS1.
  exact (fields_write_field segs mem strm _ _ zsl_SIZE 2 16 8%nat (v) H eq_refl
           ltac:(vm_compute; reflexivity) zsl_layout_within HS0 HS1).
Qed.

Lemma zsl_upd_avail_out : forall mem strm p S st v,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars (wbytes mem (zw (strm + 32)) (Z_to_le_bytes 4 (v))) strm p S (cset_avail_out st v).
Proof.
  intros mem strm p S st v H HS0 HS1.
  exact (fields_write_field segs mem strm _ _ zsl_SIZE 4 32 4%nat (v) H eq_refl
           ltac:(vm_compute; reflexivity) zsl_layout_within HS0 HS1).
Qed.

Lemma zsl_upd_total_out : forall mem strm p S st v,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars (wbytes mem (zw (strm + 40)) (Z_to_le_bytes 8 (v))) strm p S (cset_total_out st v).
Proof.
  intros mem strm p S st v H HS0 HS1.
  exact (fields_write_field segs mem strm _ _ zsl_SIZE 5 40 8%nat (v) H eq_refl
           ltac:(vm_compute; reflexivity) zsl_layout_within HS0 HS1).
Qed.



Lemma zsl_upd_adler : forall mem strm p S st v,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars (wbytes mem (zw (strm + 96)) (Z_to_le_bytes 8 (v))) strm p S (cset_adler st v).
Proof.
  intros mem strm p S st v H HS0 HS1.
  exact (fields_write_field segs mem strm _ _ zsl_SIZE 12 96 8%nat (v) H eq_refl
           ltac:(vm_compute; reflexivity) zsl_layout_within HS0 HS1).
Qed.

Lemma zsl_upd_next_out_emit : forall mem strm p S st l,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars (wbytes mem (zw (strm + 24)) (Z_to_le_bytes 8 (zp_out p + Z.of_nat (length (cs_out_rev st)) + Z.of_nat (length l))))
              strm p S (cs_emit st l).
Proof.
  intros mem strm p S st l H HS0 HS1.
  pose proof (fields_write_field segs mem strm _ _ zsl_SIZE 3 24 8%nat
                (zp_out p + Z.of_nat (length (cs_out_rev st)) + Z.of_nat (length l)) H eq_refl
                ltac:(vm_compute; reflexivity) zsl_layout_within HS0 HS1) as H'.
  unfold zsl_scalars. cbn [list_upd zsl_vals] in H'.
  unfold cs_emit, zsl_vals, cset_out_rev. cbn [cs_out_rev cs_next_in cs_avail_in cs_total_in cs_avail_out cs_total_out cs_msg cs_data_type cs_adler].
  assert (E : Z.of_nat (length (rev_append l (cs_out_rev st))) = Z.of_nat (length (cs_out_rev st)) + Z.of_nat (length l)).
  { rewrite List.rev_append_rev, length_app, length_rev. lia. }
  replace (zp_out p + Z.of_nat (length (rev_append l (cs_out_rev st))))
    with (zp_out p + Z.of_nat (length (cs_out_rev st)) + Z.of_nat (length l)) by lia.
  exact H'.
Qed.

Lemma zsl_scalars_frame : forall mem strm p S st (b : Z) bs,
  zsl_scalars mem strm p S st -> 0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (strm + zsl_SIZE <= b \/ b + Z.of_nat (length bs) <= strm) ->
  zsl_scalars (wbytes mem (zw b) bs) strm p S st.
Proof.
  intros mem strm p S st b bs H HS0 HS1 Hb0 Hb1 Hd.
  exact (fields_write_other segs mem strm _ _ zsl_SIZE b bs H zsl_layout_within HS0 HS1 Hb0 Hb1 Hd).
Qed.

Lemma zsl_scalars_agree : forall F mem mem' strm p S st,
  zsl_scalars mem strm p S st -> agree_out F mem mem' -> disj_franges F strm zsl_SIZE ->
  0 <= strm -> strm + zsl_SIZE <= 2 ^ 64 ->
  zsl_scalars mem' strm p S st.
Proof.
  intros F mem mem' strm p S st H Hag Hd HS0 HS1.
  exact (fields_agree_out segs F mem mem' strm _ _ zsl_SIZE H zsl_layout_within Hag Hd HS0 HS1).
Qed.

Lemma zsl_input_agree : forall F mem mem' p st,
  zsl_input mem p st -> agree_out F mem mem' -> disj_franges F (zp_in p) (arr_len (cs_input st)) ->
  0 <= zp_in p -> zp_in p + arr_len (cs_input st) <= 2 ^ 64 ->
  zsl_input mem' p st.
Proof.
  intros F mem mem' p st H Hag Hd H0 H1. unfold zsl_input in *.
  apply (cells_agree_out segs F mem mem' _ 1 1%nat _ _ Hag); try lia; [|exact H].
  replace (1 * arr_len (cs_input st)) with (arr_len (cs_input st)) by lia. exact Hd.
Qed.
End WithImage.
End FXG.
