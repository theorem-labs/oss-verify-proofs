(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.


Definition POLY : Z := 3988292384.

Definition xt (c : Z) : Z := Z.lxor (Z.shiftr c 1) (if Z.odd c then POLY else 0).

Fixpoint xtn (n : nat) (c : Z) : Z :=
  match n with O => c | S k => xtn k (xt c) end.


























Definition crc_step (c b : Z) : Z := xtn 8 (Z.lxor c b).

Definition crc_fold (c : Z) (bs : list Z) : Z := fold_left crc_step bs c.

Definition MASK32 : Z := 4294967295.
Definition crc32_model (init : Z) (bs : list Z) : Z :=
  Z.lxor (crc_fold (Z.lxor init MASK32) bs) MASK32.



















Definition ABASE : Z := 65521.

Fixpoint adl (bs : list Z) (s1 s2 : Z) : Z * Z :=
  match bs with
  | [] => (s1, s2)
  | b :: r => let s1' := (s1 + b) mod ABASE in
              adl r s1' ((s2 + s1') mod ABASE)
  end.


Definition adler32_model (init : Z) (bs : list Z) : Z :=
  let s1 := Z.land init 65535 in
  let s2 := Z.land (Z.shiftr init 16) 65535 in
  let (a, b) := adl bs (s1 mod ABASE) (s2 mod ABASE) in
  Z.lxor (Z.shiftl b 16) a.




Definition AMAGIC : Z := 983265 * 4294967296 + 221234637.

Definition mulhu (x y : Z) : Z := (x * y) / 18446744073709551616.









