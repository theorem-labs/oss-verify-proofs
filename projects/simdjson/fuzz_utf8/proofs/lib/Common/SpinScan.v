(* SPDX-License-Identifier: MIT *)
(** * Whether an image's executable code holds the word of [jal x0, 0]

    [exec_has_spin segs] is [true] when some segment of [segs] that is
    executable (its permission string has [x] in third place) has, in one of
    its byte strings, the hex text [6f000000] starting at an even character,
    that is at a byte boundary: the little-endian word 0x0000006f, which is
    [jal x0, 0], the instruction that jumps to itself.

    The spinning leaf of a realization ([SpinAlg.srz_spin]) and the plan
    checker's spin node ([AsanPlanCore.node_spin]) both require it.  So in an
    image whose executable segments hold no such word, no realization has a
    spinning leaf, and a realization shows that every execution ends
    ([Halts.HaltsWalk]). *)

From Stdlib Require Import ZArith NArith List Bool String Ascii.
From Stdlib Require Import PrimString Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.

Definition ss_spin_hex : PrimString.string := "6f000000"%pstring.

(** Whether [s] holds [ss_spin_hex] at character [i], [i + 2], ..., for
    [fuel] positions. *)
Fixpoint ss_hex_scan (fuel : nat) (s : PrimString.string) (i : int) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match PrimString.compare (PrimString.sub s i (PrimString.length ss_spin_hex)) ss_spin_hex with
      | Eq => true
      | _ => ss_hex_scan fuel' s (PrimInt63.add i (Uint63.of_Z 2))
      end
  end.

Definition ss_hex_has_spin (s : PrimString.string) : bool :=
  ss_hex_scan (Z.to_nat (Uint63.to_Z (PrimString.length s))) s (Uint63.of_Z 0).

Definition ss_seg_exec (sg : Segment) : bool :=
  match String.get 2 (seg_perms sg) with
  | Some c => Ascii.eqb c "x"%char
  | None => false
  end.

Definition exec_has_spin (segs : list Segment) : bool :=
  existsb (fun sg => ss_seg_exec sg && existsb ss_hex_has_spin (seg_bytes sg)) segs.
