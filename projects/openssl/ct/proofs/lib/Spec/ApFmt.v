(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Prelim PrintfModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition zdec (v : Z) : list Z := if v =? 0 then [48] else dec_digits v.
(* [comment removed for export] *)
Definition sdec (v : Z) : list Z := if v <? 0 then 45 :: zdec (- v) else zdec v.
Definition zdigits (v : Z) : Z := zlength (zdec v).
Definition sdigits (v : Z) : Z := zlength (sdec v).

(* [comment removed for export] *)
Definition padw (w : Z) (body : list Z) : Z := Z.max w (zlength body).

(* [comment removed for export] *)
Definition hdr_pieces_len (offset depth hl len : Z) (inf : bool) : list Z :=
  [ padw 5 (sdec offset) ; 3 (* [comment removed for export] *) ; padw 2 (sdec depth) ; 4 (* [comment removed for export] *) ; sdigits hl ]
  ++ (if inf then [ 8 (* [comment removed for export] *) ; 6 ] else [ 3 (* [comment removed for export] *) ; padw 4 (sdec len) ; 1 (* [comment removed for export] *) ; 6 ]).

Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

Definition hdr_len (offset depth hl len : Z) (inf : bool) : Z := zsum (hdr_pieces_len offset depth hl len inf).

(* [comment removed for export] *)
Definition dotlu_len (l : Z) : Z := 1 + zdigits l.

(* [comment removed for export] *)

(* [comment removed for export] *)
Example hdr_len_ex1 : hdr_len 0 0 2 1 false = 29.
Proof. vm_compute. reflexivity. Qed.
Example hdr_len_ex2 : hdr_len 0 0 2 0 true = 29.
Proof. vm_compute. reflexivity. Qed.
Example hdr_len_ex3 : hdr_len 100000 10 4 65536 false = 31.
Proof. vm_compute. reflexivity. Qed.
