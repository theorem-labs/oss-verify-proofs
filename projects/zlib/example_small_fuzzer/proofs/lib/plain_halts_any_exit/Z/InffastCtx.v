(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.

Module ISLayout.

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
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
  (0, 8%nat) ;
  (8, 4%nat) ;
  (12, 4%nat) ;
  (16, 4%nat) ;
  (24, 4%nat) ;
  (28, 4%nat) ;
  (32, 4%nat)  ;
  (40, 8%nat) ;
  (48, 8%nat) ;
  (56, 8%nat)  ;
  (68, 4%nat) ;
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
  (136, 4%nat) ;
  (140, 4%nat) ;
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
  S + 1384 + 4 * is_next s  ;
  is_sane s ;
  is_back s ;
  is_was s  ;
  is_reqwrap s  ;
  is_reqbits s  ].

Lemma isl_layout_within : layout_within isl_layout isl_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

Section WithImage.
Variables LF DF : Z.

Fixpoint layout_gap (L : list (Z * nat)) (o : Z) (n : Z) : bool :=
  match L with
  | [] => true
  | (o', w') :: L' => ((o + n <=? o') || (o' + Z.of_nat w' <=? o)) && layout_gap L' o n
  end.

Lemma isl_layout_gap : forall o n, 168 <= o -> 0 <= n -> o + n <= 7160 -> layout_gap isl_layout o n = true.  (* 1.4 layout (zl14infl-r2): head 168, tail at 7160 *)
Proof.
  intros o n H0 H1 H2. cbn -[Z.add Z.leb orb andb].
  repeat (apply andb_true_intro; split); try reflexivity;
    apply orb_true_intro; first [left; apply Z.leb_le; lia | right; apply Z.leb_le; lia].
Qed.
End WithImage.
End ISLayout.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z.InffastCtx.ISLayout.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Set Implicit Arguments.
Unset Implicit Arguments.



Definition ffx_of (s : inflate_state) (c : icall) (r : iregs) : ffx :=
  mkFX (ic_input c) (ic_next_in c + wrap32 (ic_avail_in c - 5))
       (ic_next_out c - wrap32 (ir_out r - ic_avail_out c))
       (ic_next_out c + wrap32 (ic_avail_out c - 257))
       (is_wsize s) (is_whave s) (is_wnext s) (is_window s)
       (zmask (is_lenbits s)) (zmask (is_distbits s)) (is_sane s).
Definition ff0_of (s : inflate_state) (c : icall) : ffs :=
  mkF (ic_next_in c) (ic_next_out c) (is_hold s) (is_bits s) 0 0 0 (FOut 0) (ic_outbuf c).

Definition ctab_len (p : codeptr) : Z :=
  match p with CDyn ofs => 1444 - ofs | CLenfix => 512 | CDistfix => 32 end.

Definition x_begm (c : icall) (r : iregs) : Z := ic_next_out c - szwrap 32 (ir_out r - ic_avail_out c).


Definition faddr (WB P0 : Z) (fr : fromptr) : Z := match fr with FWin i => WB + i | FOut i => P0 + i end.
Definition src_ok (WN bnd : Z) (fr : fromptr) : Prop := match fr with FWin i => 0 <= i < WN | FOut i => 0 <= i < bnd end.

Lemma faddr_succ : forall WB P0 fr, faddr WB P0 (from_succ fr) = faddr WB P0 fr + 1.
Proof. intros WB P0 [i|i]; cbn; lia. Qed.
Lemma faddr_add : forall WB P0 k fr, faddr WB P0 (fr_add fr k) = faddr WB P0 fr + Z.of_nat k.
Proof.
  intros WB P0 k. induction k as [|k IH]; intros fr; [cbn; lia|].
  cbn [fr_add]. rewrite IH, faddr_succ. lia.
Qed.
Lemma src_ok_weaken : forall WN b b' fr, src_ok WN b fr -> b <= b' -> src_ok WN b' fr.
Proof. intros WN b b' [i|i] H Hb; cbn in *; lia. Qed.

Definition FF0 (sp : Z) : franges := [(sp, 112)].
Definition FF1 (sp P0 ON : Z) : franges := [(sp, 112); (P0, ON)].
Definition FFall (sp P0 ON ZP S : Z) : franges :=
  [(sp, 112); (P0, ON); (ZP, 12); (ZP + 24, 12); (ZP + 48, 8); (S + 8, 4); (S + 80, 12)].

Section Facts.

End Facts.
