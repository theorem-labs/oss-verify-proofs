(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ItableMem2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ISLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastCtx.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InffastMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BvAux.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Inflate.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sA (s1 : inflate_state) : inflate_state :=
  if is_wsize s1 =? 0 then iset_whave (iset_wnext (iset_wsize s1 (shl32 1 (is_wbits s1))) 0) 0 else s1.

Definition updw_core (s : inflate_state) (src : arr) (end_ copy : Z) : inflate_state :=
  let s := sA s in
  if is_wsize s <=? copy then
    let s := iset_window s (arr_blit (is_window s) 0 src (end_ - is_wsize s) (is_wsize s)) in
    iset_whave (iset_wnext s 0) (is_wsize s)
  else
    let dist := wrap32 (is_wsize s - is_wnext s) in
    let dist := if copy <? dist then copy else dist in
    let s := iset_window s (arr_blit (is_window s) (is_wnext s) src (end_ - copy) dist) in
    let copy := wrap32 (copy - dist) in
    if negb (copy =? 0) then
      let s := iset_window s (arr_blit (is_window s) 0 src (end_ - copy) copy) in
      iset_whave (iset_wnext s copy) (is_wsize s)
    else
      let s := iset_wnext s (wrap32 (is_wnext s + dist)) in
      let s := if is_wnext s =? is_wsize s then iset_wnext s 0 else s in
      if is_whave s <? is_wsize s then iset_whave s (wrap32 (is_whave s + dist)) else s.

Definition updw_body {St} (src : arr) (end_ copy : Z) (s : inflate_state) : SM St (option inflate_state) :=
  let s := if is_wsize s =? 0
           then iset_whave (iset_wnext (iset_wsize s (shl32 1 (is_wbits s))) 0) 0
           else s in
  if is_wsize s <=? copy then
    let s := iset_window s (arr_blit (is_window s) 0 src (end_ - is_wsize s) (is_wsize s)) in
    sret (Some (iset_whave (iset_wnext s 0) (is_wsize s)))
  else
    let dist := wrap32 (is_wsize s - is_wnext s) in
    let dist := if copy <? dist then copy else dist in
    let s := iset_window s (arr_blit (is_window s) (is_wnext s) src (end_ - copy) dist) in
    let copy := wrap32 (copy - dist) in
    if negb (copy =? 0) then
      let s := iset_window s (arr_blit (is_window s) 0 src (end_ - copy) copy) in
      sret (Some (iset_whave (iset_wnext s copy) (is_wsize s)))
    else
      let s := iset_wnext s (wrap32 (is_wnext s + dist)) in
      let s := if is_wnext s =? is_wsize s then iset_wnext s 0 else s in
      let s := if is_whave s <? is_wsize s then iset_whave s (wrap32 (is_whave s + dist)) else s in
      sret (Some s).

Lemma updw_body_eq : forall {St} src end_ copy s,
  @updw_body St src end_ copy s = sret (Some (updw_core s src end_ copy)).
Proof.
  intros St src end_ copy s. unfold updw_body, updw_core, sA. cbv zeta.
  destruct (is_wsize s =? 0);
  match goal with |- (if ?c then _ else _) = _ => destruct c end; try reflexivity;
  match goal with |- (if ?c then _ else _) = _ => destruct c end; try reflexivity;
  match goal with |- (if ?c then _ else _) = _ => destruct c end; try reflexivity;
  match goal with |- (if ?c then _ else _) = _ => destruct c end; try reflexivity.
Qed.

Lemma updatewindow_unfold : forall {St} (hooks : zhooks St) s src end_ copy,
  updatewindow hooks s src end_ copy =
  sbind (match is_window_blk s with
         | Some _ => sret (Some s)
         | None =>
             sbind (zalloc hooks (shl32 1 (is_wbits s)) 1)
                   (fun r => sret (match r with
                                   | None => None
                                   | Some (b, g) => Some (iset_window (iset_window_blk s (Some b)) (iarr_u8_of g 0 (shl32 1 (is_wbits s))))
                                   end))
         end)
        (fun so => match so with None => sret None | Some s1 => updw_body src end_ copy s1 end).
Proof. intros. reflexivity. Qed.

Lemma updatewindow_some : forall {St} (hooks : zhooks St) s src end_ copy b,
  is_window_blk s = Some b -> updatewindow hooks s src end_ copy = sret (Some (updw_core s src end_ copy)).
Proof.
  intros St hooks s src end_ copy b Hb. rewrite updatewindow_unfold, Hb.
  unfold sbind at 1. unfold sret at 2. cbn [mbind fst snd].
  etransitivity; [| apply updw_body_eq]. reflexivity.
Qed.

Set Implicit Arguments.
Unset Implicit Arguments.

Section Walk.
Local Notation LFX := 0x2e260. Local Notation DFX := 0x2e1b8.

Local Ltac sepc := cbn; sep_solve.
Local Ltac srcs H := let Hc := fresh in let Hs := fresh in intros Hc; pose proof (H Hc) as Hs; unfold sep in Hs |- *; cbn; lia.

End Walk.

Section Entry.
End Entry.

Section AllocCall.
End AllocCall.

Section AllocRet.

Context {s : inflate_state} {src : arr} {pend ZP WB : Z} {sf : Z -> Z}.
End AllocRet.
