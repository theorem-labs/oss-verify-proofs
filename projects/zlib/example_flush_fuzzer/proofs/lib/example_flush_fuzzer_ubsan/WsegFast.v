(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimString PrimInt63.
From Stdlib Require Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec StreamSim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


Definition hexbyte_ok (s : PrimString.string) (i : N) : bool :=
  match hex_byte_at s i with Some _ => true | None => false end.

Fixpoint hexbytes_ok (s : PrimString.string) (off : N) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => (hexbyte_ok s off && hexbytes_ok s (off + 1)%N n')%bool
  end.

Fixpoint chunks_ok (chunks : list PrimString.string) (off : N) (n : nat) : bool :=
  match chunks with
  | [] => false
  | c :: rest =>
      let cb := Z.to_N (Uint63.to_Z (PrimString.length c) / 2) in
      if (off + N.of_nat n <=? cb)%N then hexbytes_ok c off n
      else if (cb <=? off)%N then chunks_ok rest (off - cb)%N n
      else false
  end.

Fixpoint find_segment_range (segs : list Segment) (lo hi : Z) : option Segment :=
  match segs with
  | [] => None
  | seg :: rest =>
      let base := Z.of_N (seg_base seg) in
      let top  := (base + Z.of_N (seg_size seg))%Z in
      if (Z.leb base lo && Z.leb hi top)%bool then Some seg
      else if (Z.leb hi base || Z.leb top lo)%bool then find_segment_range rest lo hi
      else None
  end.







