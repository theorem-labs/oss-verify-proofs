(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Record is_ptrs : Type := ISP { q_strm : Z; q_window : Z }.

Definition isl_SIZE : Z := 7176.
Definition isl_LENS : Z := 168.
Definition isl_WORK : Z := 808.
Definition isl_CODES : Z := 1384.

Definition codeptr_addr (LF DF S : Z) (c : codeptr) : Z :=
  match c with CDyn ofs => S + 1384 + 4 * ofs | CLenfix => LF | CDistfix => DF end.

(* zlib 1.4 (inflate.h): reqwrap after wrap, reqbits after head; the 32 old fields at their 1.4 offsets, the two
   new ones appended (reqwrap at 20, reqbits at 64) so every old position holds *)
Definition isl_layout : list (Z * nat) := [
  (0, 8%nat)  ;
  (8, 4%nat)  ;
  (12, 4%nat)  ;
  (16, 4%nat)  ;
  (24, 4%nat)  ;
  (28, 4%nat)  ;
  (32, 4%nat)  ;
  (40, 8%nat)  ;
  (48, 8%nat)  ;
  (56, 8%nat)  ;
  (68, 4%nat)  ;
  (72, 4%nat)  ;
  (76, 4%nat)  ;
  (80, 4%nat)  ;
  (88, 8%nat)  ;
  (96, 8%nat)  ;
  (104, 4%nat)  ;
  (108, 4%nat)  ;
  (112, 4%nat)  ;
  (116, 4%nat)  ;
  (120, 8%nat)  ;
  (128, 8%nat)  ;
  (136, 4%nat)  ;
  (140, 4%nat)  ;
  (144, 4%nat)  ;
  (148, 4%nat)  ;
  (152, 4%nat)  ;
  (156, 4%nat)  ;
  (160, 8%nat)  ;
  (7160, 4%nat)  ;
  (7164, 4%nat)  ;
  (7168, 4%nat)  ;
  (20, 4%nat)  ;
  (64, 4%nat)  ].

Definition isl_vals (LF DF : Z) (s : inflate_state) (p : is_ptrs) (S : Z) : list Z := [
  q_strm p  ;
  is_mode s  ;
  is_last s  ;
  is_wrap s  ;
  is_havedict s  ;
  is_flags s  ;
  is_dmax s  ;
  is_check s  ;
  is_total s  ;
  is_head s  ;
  is_wbits s  ;
  is_wsize s  ;
  is_whave s  ;
  is_wnext s  ;
  q_window p  ;
  is_hold s  ;
  is_bits s  ;
  is_length s  ;
  is_offset s  ;
  is_extra s  ;
  codeptr_addr LF DF S (is_lencode s)  ;
  codeptr_addr LF DF S (is_distcode s)  ;
  is_lenbits s  ;
  is_distbits s  ;
  is_ncode s  ;
  is_nlen s  ;
  is_ndist s  ;
  is_have s  ;
  S + 1384 + 4 * is_next s  ;
  is_sane s  ;
  is_back s  ;
  is_was s  ;
  is_reqwrap s  ;
  is_reqbits s  ].

Section WithImage.
Variables LF DF : Z.

Fixpoint layout_gap (L : list (Z * nat)) (o : Z) (n : Z) : bool :=
  match L with
  | [] => true
  | (o', w') :: L' => ((o + n <=? o') || (o' + Z.of_nat w' <=? o)) && layout_gap L' o n
  end.

End WithImage.
