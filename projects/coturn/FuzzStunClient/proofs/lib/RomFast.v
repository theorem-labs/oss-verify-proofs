(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From Stdlib Require Import Uint63.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Fixpoint to_Z_f (n : nat) (i : int) : Z :=
  match n with
  | O => 0%Z
  | S n' => if PrimInt63.eqb i 0%uint63 then 0%Z
            else (if is_even i then Z.double else Z.succ_double) (to_Z_f n' (PrimInt63.lsr i 1%uint63))
  end.

Lemma to_Z_rec_zero : forall n, to_Z_rec n 0%uint63 = 0%Z.
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [to_Z_rec].
  replace (lsr 0%uint63 1%uint63) with 0%uint63 by reflexivity. rewrite IH. reflexivity.
Qed.

Lemma to_Z_f_eq : forall n i, to_Z_f n i = to_Z_rec n i.
Proof.
  induction n as [|n IH]; intros i; [reflexivity|]. cbn [to_Z_f to_Z_rec].
  destruct (PrimInt63.eqb i 0%uint63) eqn:E.
  - apply Uint63.eqb_spec in E. subst i. symmetry. exact (to_Z_rec_zero (S n)).
  - rewrite IH. reflexivity.
Qed.

Lemma to_Z_f_to_Z i : to_Z_f 63 i = to_Z i.
Proof. exact (to_Z_f_eq 63 i). Qed.

Definition hex_nybble_f (c : char63) : N :=
  if (Uint63.leb 48 c && Uint63.leb c 57)%bool
  then Z.to_N (to_Z_f 63 c - 48)
  else if (Uint63.leb 97 c && Uint63.leb c 102)%bool
  then Z.to_N (to_Z_f 63 c - 87)
  else 16%N.

Lemma hex_nybble_f_eq c : hex_nybble_f c = hex_nybble c.
Proof. unfold hex_nybble_f, hex_nybble. rewrite !to_Z_f_to_Z. reflexivity. Qed.

Definition hex_byte_at_f (s : PrimString.string) (i : N) : option byte :=
  let ci  := Uint63.of_Z (Z.of_N (2 * i)) in
  let ci1 := Uint63.of_Z (Z.of_N (2 * i + 1)) in
  let s_len := PrimString.length s in
  if (Uint63.ltb ci1 s_len || Uint63.eqb ci1 (Uint63.sub s_len 1))%bool then
    let hi := PrimString.get s ci in
    let lo := PrimString.get s ci1 in
    let h := hex_nybble_f hi in
    let l := hex_nybble_f lo in
    if (N.ltb h 16 && N.ltb l 16)%bool
    then Some (Z_to_bv 8 (Z.of_N (h * 16 + l)))
    else None
  else None.

Lemma hex_byte_at_f_eq s i : hex_byte_at_f s i = hex_byte_at s i.
Proof. unfold hex_byte_at_f, hex_byte_at. rewrite !hex_nybble_f_eq. reflexivity. Qed.

Fixpoint segment_byte_at_f (chunks : list PrimString.string) (off : N) : option byte :=
  match chunks with
  | [] => None
  | chunk :: rest =>
      let chunk_bytes := Z.to_N (to_Z_f 63 (PrimString.length chunk) / 2) in
      if (off <? chunk_bytes)%N
      then hex_byte_at_f chunk off
      else segment_byte_at_f rest (off - chunk_bytes)
  end.

Lemma segment_byte_at_f_eq : forall chunks off, segment_byte_at_f chunks off = segment_byte_at chunks off.
Proof.
  induction chunks as [|c t IH]; intros off; [reflexivity|]. cbn [segment_byte_at_f segment_byte_at].
  rewrite to_Z_f_to_Z, hex_byte_at_f_eq, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition seg_rom_f (segs : list Segment) (addr : word) : option byte :=
  match find_segment segs (bv_unsigned addr) 1 with
  | Some seg =>
      if seg_readable seg then segment_byte_at_f (seg_bytes seg) (Z.to_N (bv_unsigned addr - Z.of_N (seg_base seg))) else None
  | None => None
  end.

Lemma seg_rom_f_eq segs addr : seg_rom_f segs addr = seg_rom segs addr.
Proof.
  unfold seg_rom_f, seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
  destruct (find_segment segs (bv_unsigned addr) 1) as [seg|]; [|reflexivity].
  destruct (seg_readable seg); [|reflexivity].
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite segment_byte_at_f_eq.
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned addr - Z.of_N (seg_base seg)))); reflexivity.
Qed.
