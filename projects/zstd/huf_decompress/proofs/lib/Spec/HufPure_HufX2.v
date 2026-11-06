(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record deltX2 := mkX2 { x2_seq : Z; x2_nbBits : Z; x2_len : Z }.
Definition x2_default : deltX2 := mkX2 0 0 0.

Definition x2_cell (dt : list deltX2) (i : Z) : res deltX2 :=
  if (0 <=? i) && (i <? Zlength dt) then Ok (nth (Z.to_nat i) dt x2_default) else Ub.

Definition x2_cell_ok (dtLog : Z) (c : deltX2) : Prop :=
  0 <= x2_seq c < 65536 /\ 0 <= x2_nbBits c <= dtLog /\ 1 <= x2_len c <= 2.

Definition x2_table_ok (dt : list deltX2) (dtLog : Z) : Prop :=
  1 <= dtLog <= HUF_TABLELOG_MAX /\ 2^dtLog <= Zlength dt /\
  forall i, 0 <= i < 2^dtLog -> x2_cell_ok dtLog (nth (Z.to_nat i) dt x2_default).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition write8 (dst : list Z) (p v : Z) : res (list Z) := store dst p (v mod 256).
Definition write16 (dst : list Z) (p v : Z) : res (list Z) :=
  let! d := store dst p (v mod 256) in store d (p + 1) ((v / 256) mod 256).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record x2state := mkX2S { x2_dst : list Z; x2_p : Z; x2_bd : bitD }.

Section DecodeX2.
  Variables (src : list Z) (dt : list deltX2) (dtLog : Z).

  (* [comment removed for export] *)
  Definition dec_x2 (x : x2state) : res x2state :=
    let v := look_bits_fast (x2_bd x) dtLog in
    let! c := x2_cell dt v in
    let! d := write16 (x2_dst x) (x2_p x) (x2_seq c) in
    Ok (mkX2S d (x2_p x + x2_len c) (skip_bits (x2_bd x) (x2_nbBits c))).

  (* [comment removed for export] *)
  Definition dec_last_x2 (x : x2state) : res x2state :=
    let v := look_bits_fast (x2_bd x) dtLog in
    let! c := x2_cell dt v in
    let! d := write8 (x2_dst x) (x2_p x) (x2_seq c) in
    let b := x2_bd x in
    let b' :=
      if x2_len c =? 1 then skip_bits b (x2_nbBits c)
      else if bd_bits b <? 64 then
             let b1 := skip_bits b (x2_nbBits c) in
             if 64 <? bd_bits b1 then mkBD (bd_cont b1) 64 (bd_ptr b1) (bd_zero b1) else b1
           else b in
    Ok (mkX2S d (x2_p x + 1) b').

  Fixpoint dec_n (n : nat) (x : x2state) : res x2state :=
    match n with O => Ok x | S k => let! x' := dec_x2 x in dec_n k x' end.

  Definition with_bd (x : x2state) (d : bitD) : x2state := mkX2S (x2_dst x) (x2_p x) d.

  (* [comment removed for export] *)
  Fixpoint loopR (fuel : nat) (k : nat) (m : Z) (pEnd : Z) (x : x2state) : res x2state :=
    match fuel with
    | O => NoFuel
    | S f =>
        let! r := reload_dstream src (x2_bd x) in
        let '(st, d) := r in
        let x := with_bd x d in
        if dstatus_eqb st Unfinished && (x2_p x <? pEnd - m)
        then let! x' := dec_n k x in loopR f k m pEnd x'
        else Ok x
    end.

  (* [comment removed for export] *)
  Fixpoint loopT (fuel : nat) (pEnd : Z) (x : x2state) : res x2state :=
    match fuel with
    | O => NoFuel
    | S f => if x2_p x <=? pEnd - 2 then let! x' := dec_x2 x in loopT f pEnd x' else Ok x
    end.

  (* [comment removed for export] *)
  Definition decode_stream_x2 (pEnd : Z) (x : x2state) : res x2state :=
    let n := pEnd - x2_p x in
    let fuel := S (Z.to_nat n) in
    let! x := (if 8 <=? n then
                 (if dtLog <=? 11 then loopR fuel 5 9 pEnd x else loopR fuel 4 7 pEnd x)
               else let! r := reload_dstream src (x2_bd x) in let '(_, d) := r in Ok (with_bd x d)) in
    let! x := (if 2 <=? pEnd - x2_p x then
                 (* [comment removed for export] *)
                 let! x := loopR fuel 1 1 pEnd x in loopT fuel pEnd x
               else Ok x) in
    if x2_p x <? pEnd then dec_last_x2 x else Ok x.

  (* [comment removed for export] *)
  Definition decompress1X2 (dst0 : list Z) : res (list Z) :=
    let! d := init_dstream src in
    let! x := decode_stream_x2 (Zlength dst0) (mkX2S dst0 0 d) in
    if end_of_dstream (x2_bd x) then Ok (x2_dst x) else Err ZSTD_error_corruption_detected.
End DecodeX2.
