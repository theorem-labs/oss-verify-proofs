(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface InflateState.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Record is_ptrs : Type := ISP { q_strm : Z; q_window : Z }.

Definition isl_SIZE : Z := 7176.
Definition codeptr_addr (LF DF S : Z) (c : codeptr) : Z :=
  match c with CDyn ofs => S + 1384 + 4 * ofs | CLenfix => LF | CDistfix => DF end.

Definition isl_layout : list (Z * nat) := [
  (0, 8%nat) ;
  (8, 4%nat) ;
  (12, 4%nat) ;
  (16, 4%nat) ;
  (24, 4%nat) ;
  (28, 4%nat) ;
  (32, 4%nat) ;
  (40, 8%nat) ;
  (48, 8%nat) ;
  (56, 8%nat) ;
  (68, 4%nat) ;
  (72, 4%nat) ;
  (76, 4%nat) ;
  (80, 4%nat) ;
  (88, 8%nat) ;
  (96, 8%nat) ;
  (104, 4%nat) ;
  (108, 4%nat) ;
  (112, 4%nat) ;
  (116, 4%nat) ;
  (120, 8%nat) ;
  (128, 8%nat) ;
  (136, 4%nat) ;
  (140, 4%nat) ;
  (144, 4%nat) ;
  (148, 4%nat) ;
  (152, 4%nat) ;
  (156, 4%nat) ;
  (160, 8%nat) ;
  (7160, 4%nat) ;
  (7164, 4%nat) ;
  (7168, 4%nat) ;
  (20, 4%nat) (* zlib 1.4: reqwrap *);
  (64, 4%nat) (* zlib 1.4: reqbits *)].

Definition isl_vals (LF DF : Z) (s : inflate_state) (p : is_ptrs) (S : Z) : list Z := [
  q_strm p ;
  is_mode s ;
  is_last s ;
  is_wrap s ;
  is_havedict s ;
  is_flags s ;
  is_dmax s ;
  is_check s ;
  is_total s ;
  is_head s ;
  is_wbits s ;
  is_wsize s ;
  is_whave s ;
  is_wnext s ;
  q_window p ;
  is_hold s ;
  is_bits s ;
  is_length s ;
  is_offset s ;
  is_extra s ;
  codeptr_addr LF DF S (is_lencode s) ;
  codeptr_addr LF DF S (is_distcode s) ;
  is_lenbits s ;
  is_distbits s ;
  is_ncode s ;
  is_nlen s ;
  is_ndist s ;
  is_have s ;
  S + 1384 + 4 * is_next s ;
  is_sane s ;
  is_back s ;
  is_was s ;
  5 (* zlib 1.4: reqwrap = wrap of inflateInit_ (windowBits 15) *);
  15 (* zlib 1.4: reqbits = windowBits 15 *)].

Lemma isl_layout_within : layout_within isl_layout isl_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

Section WithImage.
Variable segs : list Segment.
Variables LF DF : Z.

Definition isl_scalars (mem : word -> option byte) (S : Z) (p : is_ptrs) (s : inflate_state) : Prop :=
  fields segs mem S isl_layout (isl_vals LF DF s p S).


Lemma isl_strm : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 0) 8 (q_strm p).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 0 0 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_mode : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 8) 4 (is_mode s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 1 8 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_last : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 12) 4 (is_last s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 2 12 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_wrap : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 16) 4 (is_wrap s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 3 16 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_havedict : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 24) 4 (is_havedict s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 4 24 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_flags : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 28) 4 (is_flags s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 5 28 4%nat _ H eq_refl eq_refl). Qed.


Lemma isl_check : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 40) 8 (is_check s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 7 40 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_total : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 48) 8 (is_total s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 8 48 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_head : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 56) 8 (is_head s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 9 56 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_wbits : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 68) 4 (is_wbits s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 10 68 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_wsize : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 72) 4 (is_wsize s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 11 72 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_whave : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 76) 4 (is_whave s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 12 76 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_wnext : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 80) 4 (is_wnext s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 13 80 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_window : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 88) 8 (q_window p).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 14 88 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_hold : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 96) 8 (is_hold s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 15 96 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_bits : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 104) 4 (is_bits s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 16 104 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_length : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 108) 4 (is_length s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 17 108 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_offset : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 112) 4 (is_offset s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 18 112 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_extra : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 116) 4 (is_extra s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 19 116 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_lencode : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 120) 8 (codeptr_addr LF DF S (is_lencode s)).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 20 120 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_distcode : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 128) 8 (codeptr_addr LF DF S (is_distcode s)).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 21 128 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_lenbits : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 136) 4 (is_lenbits s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 22 136 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_distbits : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 140) 4 (is_distbits s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 23 140 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_ncode : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 144) 4 (is_ncode s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 24 144 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_nlen : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 148) 4 (is_nlen s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 25 148 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_ndist : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 152) 4 (is_ndist s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 26 152 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_have : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 156) 4 (is_have s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 27 156 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_next : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 160) 8 (S + 1384 + 4 * is_next s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 28 160 8%nat _ H eq_refl eq_refl). Qed.

Lemma isl_sane : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 7160) 4 (is_sane s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 29 7160 4%nat _ H eq_refl eq_refl). Qed.

Lemma isl_back : forall mem S p s, isl_scalars mem S p s -> cell segs mem (S + 7164) 4 (is_back s).
Proof. intros mem S p s H. exact (fields_nth segs mem S _ _ 30 7164 4%nat _ H eq_refl eq_refl). Qed.



Lemma isl_upd_mode : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 8)) (Z_to_le_bytes 4 v)) S p (iset_mode s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 1 8 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_last : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 12)) (Z_to_le_bytes 4 v)) S p (iset_last s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 2 12 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_wrap : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 16)) (Z_to_le_bytes 4 v)) S p (iset_wrap s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 3 16 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_havedict : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 24)) (Z_to_le_bytes 4 v)) S p (iset_havedict s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 4 24 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_flags : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 28)) (Z_to_le_bytes 4 v)) S p (iset_flags s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 5 28 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_dmax : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 32)) (Z_to_le_bytes 4 v)) S p (iset_dmax s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 6 32 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_check : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 40)) (Z_to_le_bytes 8 v)) S p (iset_check s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 7 40 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_total : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 48)) (Z_to_le_bytes 8 v)) S p (iset_total s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 8 48 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_head : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 56)) (Z_to_le_bytes 8 v)) S p (iset_head s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 9 56 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.


Lemma isl_upd_wsize : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 72)) (Z_to_le_bytes 4 v)) S p (iset_wsize s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 11 72 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_whave : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 76)) (Z_to_le_bytes 4 v)) S p (iset_whave s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 12 76 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_wnext : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 80)) (Z_to_le_bytes 4 v)) S p (iset_wnext s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 13 80 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_window : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 88)) (Z_to_le_bytes 8 v)) S (ISP (q_strm p) v) s.
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 14 88 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_hold : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 96)) (Z_to_le_bytes 8 v)) S p (iset_hold s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 15 96 8%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_bits : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 104)) (Z_to_le_bytes 4 v)) S p (iset_bits s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 16 104 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_length : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 108)) (Z_to_le_bytes 4 v)) S p (iset_length s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 17 108 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_offset : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 112)) (Z_to_le_bytes 4 v)) S p (iset_offset s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 18 112 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_extra : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 116)) (Z_to_le_bytes 4 v)) S p (iset_extra s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 19 116 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_lencode : forall mem S p s (c : codeptr),
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 120)) (Z_to_le_bytes 8 (codeptr_addr LF DF S c))) S p (iset_lencode s c).
Proof.
  intros mem S p s c H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 20 120 8%nat (codeptr_addr LF DF S c) H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_distcode : forall mem S p s (c : codeptr),
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 128)) (Z_to_le_bytes 8 (codeptr_addr LF DF S c))) S p (iset_distcode s c).
Proof.
  intros mem S p s c H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 21 128 8%nat (codeptr_addr LF DF S c) H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_lenbits : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 136)) (Z_to_le_bytes 4 v)) S p (iset_lenbits s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 22 136 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_distbits : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 140)) (Z_to_le_bytes 4 v)) S p (iset_distbits s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 23 140 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_ncode : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 144)) (Z_to_le_bytes 4 v)) S p (iset_ncode s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 24 144 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_nlen : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 148)) (Z_to_le_bytes 4 v)) S p (iset_nlen s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 25 148 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_ndist : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 152)) (Z_to_le_bytes 4 v)) S p (iset_ndist s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 26 152 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_have : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 156)) (Z_to_le_bytes 4 v)) S p (iset_have s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 27 156 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_next : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 160)) (Z_to_le_bytes 8 (S + 1384 + 4 * v))) S p (iset_next s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 28 160 8%nat (S + 1384 + 4 * v) H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_sane : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 7160)) (Z_to_le_bytes 4 v)) S p (iset_sane s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 29 7160 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_back : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 7164)) (Z_to_le_bytes 4 v)) S p (iset_back s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 30 7164 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Lemma isl_upd_was : forall mem S p s v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars (wbytes mem (zw (S + 7168)) (Z_to_le_bytes 4 v)) S p (iset_was s v).
Proof.
  intros mem S p s v H HS0 HS1.
  exact (fields_write_field segs mem S _ _ isl_SIZE 31 7168 4%nat v H eq_refl
           ltac:(vm_compute; reflexivity) isl_layout_within HS0 HS1).
Qed.

Fixpoint layout_gap (L : list (Z * nat)) (o : Z) (n : Z) : bool :=
  match L with
  | [] => true
  | (o', w') :: L' => ((o + n <=? o') || (o' + Z.of_nat w' <=? o)) && layout_gap L' o n
  end.

Lemma fields_write_gap : forall L mem Sb vs (o : Z) bs,
  fields segs mem Sb L vs -> layout_gap L o (Z.of_nat (length bs)) = true ->
  layout_within L isl_SIZE = true ->
  0 <= Sb -> Sb + isl_SIZE <= 2 ^ 64 -> 0 <= o -> o + Z.of_nat (length bs) <= isl_SIZE ->
  fields segs (wbytes mem (zw (Sb + o)) bs) Sb L vs.
Proof.
  induction L as [|[o' w'] L' IH]; intros mem Sb vs o bs Hf HG HW HS0 HS1 Ho Hon.
  - destruct vs; [exact I | destruct Hf].
  - destruct vs as [|v vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_gap] in HG. apply andb_prop in HG as [HG HG'].
    cbn [layout_within] in HW. apply andb_prop in HW as [HW HW']. apply andb_prop in HW as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    split; [| exact (IH mem Sb vs' o bs Hf' HG' HW' HS0 HS1 Ho Hon)].
    apply cell_write_other; [exact Hc | lia | lia | lia | lia |].
    apply orb_prop in HG as [HG|HG]; apply Z.leb_le in HG; [right | left]; lia.
Qed.

Lemma isl_layout_gap : forall o n, 168 <= o -> 0 <= n -> o + n <= 7160 -> layout_gap isl_layout o n = true.  (* 1.4: arrays at 168 .. 7160 *)
Proof.
  intros o n H0 H1 H2. cbn -[Z.add Z.leb orb andb].
  repeat (apply andb_true_intro; split); try reflexivity;
    apply orb_true_intro; first [left; apply Z.leb_le; lia | right; apply Z.leb_le; lia].
Qed.

Lemma isl_scalars_write_arrays : forall mem S p s (o : Z) bs,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  168 <= o -> o + Z.of_nat (length bs) <= 7160 ->
  isl_scalars (wbytes mem (zw (S + o)) bs) S p s.
Proof.
  intros mem S p s o bs H HS0 HS1 Ho Hon. unfold isl_scalars in *.
  apply fields_write_gap; try (unfold isl_SIZE in *; lia); [exact H | | exact isl_layout_within].
  apply isl_layout_gap; lia.
Qed.

Lemma isl_scalars_lens_cell : forall mem S p s i v,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 -> 0 <= i < 320 ->
  isl_scalars (wbytes mem (zw (S + 168 + 2 * i)) (Z_to_le_bytes 2 v)) S p s.
Proof.
  intros mem S p s i v H HS0 HS1 Hi. rewrite <- Z.add_assoc.
  apply isl_scalars_write_arrays; rewrite ?length_Z_to_le_bytes; try assumption; cbn; lia.
Qed.



Lemma isl_scalars_frame : forall mem S p s (b : Z) bs,
  isl_scalars mem S p s -> 0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (S + isl_SIZE <= b \/ b + Z.of_nat (length bs) <= S) ->
  isl_scalars (wbytes mem (zw b) bs) S p s.
Proof.
  intros mem S p s b bs H HS0 HS1 Hb0 Hb1 Hd.
  exact (fields_write_other segs mem S _ _ isl_SIZE b bs H isl_layout_within HS0 HS1 Hb0 Hb1 Hd).
Qed.

Lemma isl_scalars_agree : forall F mem mem' S p s,
  isl_scalars mem S p s -> agree_out F mem mem' -> disj_franges F S isl_SIZE ->
  0 <= S -> S + isl_SIZE <= 2 ^ 64 ->
  isl_scalars mem' S p s.
Proof.
  intros F mem mem' S p s H Hag Hd HS0 HS1.
  exact (fields_agree_out segs F mem mem' S _ _ isl_SIZE H isl_layout_within Hag Hd HS0 HS1).
Qed.

End WithImage.
End FXG.
