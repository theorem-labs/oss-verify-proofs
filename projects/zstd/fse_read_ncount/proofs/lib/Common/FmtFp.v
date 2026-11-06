(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SoftFloat.
Notation "'let?' x ':=' e 'in' k" :=
(match e with Some x => k | None => None end)
(at level 200, x pattern, e at level 100, k at level 200, only parsing).
Inductive flow (A : Type) : Type := Ret : Z -> flow A | Cont : A -> flow A.
Arguments Ret {A} _. Arguments Cont {A} _.
Definition ALT_FORM : Z := 8.
Definition ZERO_PAD : Z := 65536.
Definition LEFT_ADJ : Z := 8192.
Definition PAD_POS : Z := 1.
Definition MARK_POS : Z := 2048.
Definition INT_MAX : Z := 2147483647.
Definition INTMAX_MAX : Z := 9223372036854775807.
Definition PAD_FUEL := 64%nat.
Definition out (o bytes : list Z) : list Z := o ++ bytes.
Definition pad_loop_body (c : Z) (s : Z * list Z) : Z * list Z :=
let '(l, o) := s in
let o := out o (zrepeat c 256) in
(l - 256, o).
Fixpoint pad_loop (c : Z) (fuel : nat) (s : Z * list Z) {struct fuel} : option (Z * list Z) :=
match fuel with
| O => None
| S fuel' =>
let '(l, o) := s in
if 256 <=? l then pad_loop c fuel' (pad_loop_body c s) else Some s
end.
Definition pad (o : list Z) (c w l fl : Z) : option (list Z) :=
if negb (Z.land fl (Z.lor LEFT_ADJ ZERO_PAD) =? 0) || (w <=? l) then Some o
else
let l := w - l in
let? (l, o) := pad_loop c PAD_FUEL (l, o) in
Some (out o (zrepeat c l)).
