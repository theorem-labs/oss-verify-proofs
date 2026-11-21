(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec SeqExec StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Export ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.

Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.
Definition is6_SIZE : Z := 7176.
Definition is6_LENFIX : Z := 75438.
Definition is6_DISTFIX : Z := 77486.
Definition is6_layout : list (Z * nat) := isl_layout.
Definition is6_vals (s : inflate_state) (p : is_ptrs) (S : Z) : list Z := isl_vals 75438 77486 s p S.
Definition is6_scalars (mem : word -> option byte) (S : Z) (p : is_ptrs) (s : inflate_state) : Prop :=
  fields s6u_segs mem S is6_layout (is6_vals s p S).
Lemma is6_scalars_isl : forall mem S p s, is6_scalars mem S p s = isl_scalars s6u_segs 75438 77486 mem S p s.
Proof. reflexivity. Qed.
Lemma is6_layout_within : layout_within is6_layout is6_SIZE = true.
Proof. exact isl_layout_within. Qed.
Definition is6_lensA (mem : word -> option byte) (S : Z) (s : inflate_state) : Prop :=
  cells s6u_segs mem (S + 168) 2 2 320 (arr_get (is_lens s)).
Definition is6_workA (mem : word -> option byte) (S : Z) (s : inflate_state) : Prop :=
  cells s6u_segs mem (S + 808) 2 2 288 (arr_get (is_work s)).
Definition is6_codesA (mem : word -> option byte) (S : Z) (s : inflate_state) : Prop :=
  cells s6u_segs mem (S + 1384) 4 4 1444 (arr_get (is_codes s)).
Definition is6_arrays (mem : word -> option byte) (S : Z) (s : inflate_state) : Prop :=
  is6_lensA mem S s /\ is6_workA mem S s /\ is6_codesA mem S s.

Lemma is6_strm : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 0) 8 (q_strm p).
Proof. exact (isl_strm s6u_segs 75438 77486). Qed.

Lemma is6_mode : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 8) 4 (is_mode s).
Proof. exact (isl_mode s6u_segs 75438 77486). Qed.

Lemma is6_last : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 12) 4 (is_last s).
Proof. exact (isl_last s6u_segs 75438 77486). Qed.

Lemma is6_wrap : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 16) 4 (is_wrap s).
Proof. exact (isl_wrap s6u_segs 75438 77486). Qed.

Lemma is6_havedict : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 24) 4 (is_havedict s).
Proof. exact (isl_havedict s6u_segs 75438 77486). Qed.

Lemma is6_flags : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 28) 4 (is_flags s).
Proof. exact (isl_flags s6u_segs 75438 77486). Qed.


Lemma is6_check : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 40) 8 (is_check s).
Proof. exact (isl_check s6u_segs 75438 77486). Qed.

Lemma is6_total : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 48) 8 (is_total s).
Proof. exact (isl_total s6u_segs 75438 77486). Qed.

Lemma is6_head : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 56) 8 (is_head s).
Proof. exact (isl_head s6u_segs 75438 77486). Qed.

Lemma is6_wbits : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 68) 4 (is_wbits s).
Proof. exact (isl_wbits s6u_segs 75438 77486). Qed.

Lemma is6_wsize : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 72) 4 (is_wsize s).
Proof. exact (isl_wsize s6u_segs 75438 77486). Qed.

Lemma is6_whave : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 76) 4 (is_whave s).
Proof. exact (isl_whave s6u_segs 75438 77486). Qed.

Lemma is6_wnext : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 80) 4 (is_wnext s).
Proof. exact (isl_wnext s6u_segs 75438 77486). Qed.

Lemma is6_window : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 88) 8 (q_window p).
Proof. exact (isl_window s6u_segs 75438 77486). Qed.

Lemma is6_hold : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 96) 8 (is_hold s).
Proof. exact (isl_hold s6u_segs 75438 77486). Qed.

Lemma is6_bits : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 104) 4 (is_bits s).
Proof. exact (isl_bits s6u_segs 75438 77486). Qed.

Lemma is6_length : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 108) 4 (is_length s).
Proof. exact (isl_length s6u_segs 75438 77486). Qed.

Lemma is6_offset : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 112) 4 (is_offset s).
Proof. exact (isl_offset s6u_segs 75438 77486). Qed.

Lemma is6_extra : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 116) 4 (is_extra s).
Proof. exact (isl_extra s6u_segs 75438 77486). Qed.

Lemma is6_lencode : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 120) 8 (codeptr_addr 75438 77486 S (is_lencode s)).
Proof. exact (isl_lencode s6u_segs 75438 77486). Qed.

Lemma is6_distcode : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 128) 8 (codeptr_addr 75438 77486 S (is_distcode s)).
Proof. exact (isl_distcode s6u_segs 75438 77486). Qed.

Lemma is6_lenbits : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 136) 4 (is_lenbits s).
Proof. exact (isl_lenbits s6u_segs 75438 77486). Qed.

Lemma is6_distbits : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 140) 4 (is_distbits s).
Proof. exact (isl_distbits s6u_segs 75438 77486). Qed.

Lemma is6_ncode : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 144) 4 (is_ncode s).
Proof. exact (isl_ncode s6u_segs 75438 77486). Qed.

Lemma is6_nlen : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 148) 4 (is_nlen s).
Proof. exact (isl_nlen s6u_segs 75438 77486). Qed.

Lemma is6_ndist : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 152) 4 (is_ndist s).
Proof. exact (isl_ndist s6u_segs 75438 77486). Qed.

Lemma is6_have : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 156) 4 (is_have s).
Proof. exact (isl_have s6u_segs 75438 77486). Qed.

Lemma is6_next : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 160) 8 (S + 1384 + 4 * is_next s).
Proof. exact (isl_next s6u_segs 75438 77486). Qed.

Lemma is6_sane : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 7160) 4 (is_sane s).
Proof. exact (isl_sane s6u_segs 75438 77486). Qed.

Lemma is6_back : forall mem S p s, is6_scalars mem S p s -> cell s6u_segs mem (S + 7164) 4 (is_back s).
Proof. exact (isl_back s6u_segs 75438 77486). Qed.



Lemma is6_upd_mode : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 8)) (Z_to_le_bytes 4 v)) S p (iset_mode s v).
Proof. exact (isl_upd_mode s6u_segs 75438 77486). Qed.

Lemma is6_upd_last : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 12)) (Z_to_le_bytes 4 v)) S p (iset_last s v).
Proof. exact (isl_upd_last s6u_segs 75438 77486). Qed.

Lemma is6_upd_wrap : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 16)) (Z_to_le_bytes 4 v)) S p (iset_wrap s v).
Proof. exact (isl_upd_wrap s6u_segs 75438 77486). Qed.

Lemma is6_upd_havedict : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 24)) (Z_to_le_bytes 4 v)) S p (iset_havedict s v).
Proof. exact (isl_upd_havedict s6u_segs 75438 77486). Qed.

Lemma is6_upd_flags : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 28)) (Z_to_le_bytes 4 v)) S p (iset_flags s v).
Proof. exact (isl_upd_flags s6u_segs 75438 77486). Qed.

Lemma is6_upd_dmax : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 32)) (Z_to_le_bytes 4 v)) S p (iset_dmax s v).
Proof. exact (isl_upd_dmax s6u_segs 75438 77486). Qed.

Lemma is6_upd_check : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 40)) (Z_to_le_bytes 8 v)) S p (iset_check s v).
Proof. exact (isl_upd_check s6u_segs 75438 77486). Qed.

Lemma is6_upd_total : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 48)) (Z_to_le_bytes 8 v)) S p (iset_total s v).
Proof. exact (isl_upd_total s6u_segs 75438 77486). Qed.

Lemma is6_upd_head : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 56)) (Z_to_le_bytes 8 v)) S p (iset_head s v).
Proof. exact (isl_upd_head s6u_segs 75438 77486). Qed.


Lemma is6_upd_wsize : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 72)) (Z_to_le_bytes 4 v)) S p (iset_wsize s v).
Proof. exact (isl_upd_wsize s6u_segs 75438 77486). Qed.

Lemma is6_upd_whave : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 76)) (Z_to_le_bytes 4 v)) S p (iset_whave s v).
Proof. exact (isl_upd_whave s6u_segs 75438 77486). Qed.

Lemma is6_upd_wnext : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 80)) (Z_to_le_bytes 4 v)) S p (iset_wnext s v).
Proof. exact (isl_upd_wnext s6u_segs 75438 77486). Qed.

Lemma is6_upd_window : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 88)) (Z_to_le_bytes 8 v)) S (ISP (q_strm p) v) s.
Proof. exact (isl_upd_window s6u_segs 75438 77486). Qed.

Lemma is6_upd_hold : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 96)) (Z_to_le_bytes 8 v)) S p (iset_hold s v).
Proof. exact (isl_upd_hold s6u_segs 75438 77486). Qed.

Lemma is6_upd_bits : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 104)) (Z_to_le_bytes 4 v)) S p (iset_bits s v).
Proof. exact (isl_upd_bits s6u_segs 75438 77486). Qed.

Lemma is6_upd_length : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 108)) (Z_to_le_bytes 4 v)) S p (iset_length s v).
Proof. exact (isl_upd_length s6u_segs 75438 77486). Qed.

Lemma is6_upd_offset : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 112)) (Z_to_le_bytes 4 v)) S p (iset_offset s v).
Proof. exact (isl_upd_offset s6u_segs 75438 77486). Qed.

Lemma is6_upd_extra : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 116)) (Z_to_le_bytes 4 v)) S p (iset_extra s v).
Proof. exact (isl_upd_extra s6u_segs 75438 77486). Qed.

Lemma is6_upd_lencode : forall mem S p s (c : codeptr),
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 120)) (Z_to_le_bytes 8 (codeptr_addr 75438 77486 S c))) S p (iset_lencode s c).
Proof. exact (isl_upd_lencode s6u_segs 75438 77486). Qed.

Lemma is6_upd_distcode : forall mem S p s (c : codeptr),
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 128)) (Z_to_le_bytes 8 (codeptr_addr 75438 77486 S c))) S p (iset_distcode s c).
Proof. exact (isl_upd_distcode s6u_segs 75438 77486). Qed.

Lemma is6_upd_lenbits : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 136)) (Z_to_le_bytes 4 v)) S p (iset_lenbits s v).
Proof. exact (isl_upd_lenbits s6u_segs 75438 77486). Qed.

Lemma is6_upd_distbits : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 140)) (Z_to_le_bytes 4 v)) S p (iset_distbits s v).
Proof. exact (isl_upd_distbits s6u_segs 75438 77486). Qed.

Lemma is6_upd_ncode : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 144)) (Z_to_le_bytes 4 v)) S p (iset_ncode s v).
Proof. exact (isl_upd_ncode s6u_segs 75438 77486). Qed.

Lemma is6_upd_nlen : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 148)) (Z_to_le_bytes 4 v)) S p (iset_nlen s v).
Proof. exact (isl_upd_nlen s6u_segs 75438 77486). Qed.

Lemma is6_upd_ndist : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 152)) (Z_to_le_bytes 4 v)) S p (iset_ndist s v).
Proof. exact (isl_upd_ndist s6u_segs 75438 77486). Qed.

Lemma is6_upd_have : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 156)) (Z_to_le_bytes 4 v)) S p (iset_have s v).
Proof. exact (isl_upd_have s6u_segs 75438 77486). Qed.

Lemma is6_upd_next : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 160)) (Z_to_le_bytes 8 (S + 1384 + 4 * v))) S p (iset_next s v).
Proof. exact (isl_upd_next s6u_segs 75438 77486). Qed.

Lemma is6_upd_sane : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 7160)) (Z_to_le_bytes 4 v)) S p (iset_sane s v).
Proof. exact (isl_upd_sane s6u_segs 75438 77486). Qed.

Lemma is6_upd_back : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 7164)) (Z_to_le_bytes 4 v)) S p (iset_back s v).
Proof. exact (isl_upd_back s6u_segs 75438 77486). Qed.

Lemma is6_upd_was : forall mem S p s v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars (wbytes mem (zw (S + 7168)) (Z_to_le_bytes 4 v)) S p (iset_was s v).
Proof. exact (isl_upd_was s6u_segs 75438 77486). Qed.

Lemma is6_scalars_lens_cell : forall mem S p s i v,
  is6_scalars mem S p s -> 0 <= S -> S + is6_SIZE <= 2 ^ 64 -> 0 <= i < 320 ->
  is6_scalars (wbytes mem (zw (S + 168 + 2 * i)) (Z_to_le_bytes 2 v)) S p s.
Proof. exact (isl_scalars_lens_cell s6u_segs 75438 77486). Qed.


Lemma is6_scalars_agree : forall F mem mem' S p s,
  is6_scalars mem S p s -> agree_out F mem mem' -> disj_franges F S is6_SIZE ->
  0 <= S -> S + is6_SIZE <= 2 ^ 64 ->
  is6_scalars mem' S p s.
Proof. exact (isl_scalars_agree s6u_segs 75438 77486). Qed.
End FXG.
