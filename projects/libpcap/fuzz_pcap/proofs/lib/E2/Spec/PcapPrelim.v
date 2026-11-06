(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Fmt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition INT_MAX : Z := 2^31 - 1.
Definition UINT_MAX : Z := 2^32 - 1.

(* [comment removed for export] *)
Definition zfirstn {A} (n : Z) (l : list A) : list A := firstn (Z.to_nat n) l.
Definition zskipn {A} (n : Z) (l : list A) : list A := skipn (Z.to_nat n) l.
(* [comment removed for export] *)
Definition zslice {A} (off n : Z) (l : list A) : list A := zfirstn n (zskipn off l).

(* [comment removed for export] *)
Fixpoint le_of_bytes (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: bs' => b + 256 * le_of_bytes bs'
  end.
Definition get_u8   (buf : list Z) (off : Z) : Z := znth buf off.
Definition get_le16 (buf : list Z) (off : Z) : Z := le_of_bytes (zslice off 2 buf).
Definition get_le32 (buf : list Z) (off : Z) : Z := le_of_bytes (zslice off 4 buf).
Definition get_le64 (buf : list Z) (off : Z) : Z := le_of_bytes (zslice off 8 buf).
(* [comment removed for export] *)
Definition get_be16 (buf : list Z) (off : Z) : Z := get_u8 buf off * 256 + get_u8 buf (off + 1).

(* [comment removed for export] *)
Fixpoint le_bytes_nat (k : nat) (v : Z) : list Z :=
  match k with
  | O => []
  | S k' => (v mod 256) :: le_bytes_nat k' (v / 256)
  end.
Definition le_bytes (k : Z) (v : Z) : list Z := le_bytes_nat (Z.to_nat k) v.

(* [comment removed for export] *)
Definition bswap16 (v : Z) : Z := le_of_bytes (rev (le_bytes 2 v)).
Definition bswap32 (v : Z) : Z := le_of_bytes (rev (le_bytes 4 v)).
Definition bswap64 (v : Z) : Z := le_of_bytes (rev (le_bytes 8 v)).

(* [comment removed for export] *)
Definition buf_write_at (off : Z) (bytes : list Z) (buf : list Z) : list Z :=
  zfirstn off buf ++ bytes ++ zskipn (off + zlength bytes) buf.

(* [comment removed for export] *)
Definition swap_field (k : Z) (off : Z) (buf : list Z) : list Z :=
  buf_write_at off (rev (zslice off k buf)) buf.

(* [comment removed for export] *)
Fixpoint cstr (l : list Z) : list Z :=
  match l with
  | [] => []
  | c :: l' => if c =? 0 then [] else c :: cstr l'
  end.

(* [comment removed for export] *)
Example bswap32_ex : bswap32 2712847316 (* [comment removed for export] *) = 3569595041 (* [comment removed for export] *).
Proof. vm_compute. reflexivity. Qed.
Example bswap16_ex : bswap16 258 = 513. Proof. vm_compute. reflexivity. Qed.
Example buf_write_at_ex : buf_write_at 1 [9;9] [0;1;2;3;4] = [0;9;9;3;4].
Proof. vm_compute. reflexivity. Qed.
Example swap_field_ex : swap_field 4 1 [0;1;2;3;4;5] = [0;4;3;2;1;5].
Proof. vm_compute. reflexivity. Qed.
Example get_le32_ex : get_le32 [0;212;195;178;161;9] 1 = 2712847316.
Proof. vm_compute. reflexivity. Qed.
Example le_bytes_ex : le_bytes 4 2712847316 = [212;195;178;161].
Proof. vm_compute. reflexivity. Qed.
