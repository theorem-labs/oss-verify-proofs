(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/InitLib.v's auxv table: the start state's auxv region at LPS 727298f3 (27 or 29 pairs, AT_EGID's value AT_GID's background word) per CONFIG_RSEQ value, and the region both values imply; AT_PHNUM's value the image's program-header count, 10 for the plain images (R3Tb, R3A) and 11 for the ASan and ASan+UBSan images (R3Tb_asan, R3A_asan). *)
(* The auxv region (region 3) of the start state at LPS 727298f3, one per CONFIG_RSEQ value, and the
   region the main phase's templates keep for it at both values.  Moved here from [Glue/InitLib.v] so the
   certificate data can name it.

   [StackLayout.auxv_entries] lays down 27 pairs, or 29 with CONFIG_RSEQ, in the order of [aux_types];
   [Ctr.DefsA]'s [AUXV_KEYS] and [AUXV_RSEQ_KEYS] read the same order.  Every type word is a cell.  A
   value word is a cell only where the plan names its value; the launch-chosen ones (SYSINFO_EHDR, the
   eight cache words, MINSIGSTKSZ, ENTRY, GID, EXECFN) are the region's [BGUnk] background, read off the
   vector's own bytes.  AT_EGID's value is a cell holding AT_GID's background word: the model gives both
   the run's gid ([StackLayout.auxv_entries]), so musl's [aux[AT_GID] == aux[AT_EGID]] test in
   [__init_libc] compares one term with itself and decides.  AT_PHNUM's value is the image's
   program-header count: 10 for the plain images ([R3Tb], [R3A]; Glue/InitSrc2.v's [phN]), 11 for the
   ASan and ASan+UBSan images ([R3Tb_asan], [R3A_asan]; AS/AsanPlanCore.v's atables, which
   AS/AsanInit.v's [img_facts] ties to the image). *)
From Stdlib Require Import ZArith List.
From Stdlib Require Import PrimInt63 Uint63.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Notation.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations W64 Val Mem.

Module Auxv.

Definition aux_types (b : bool) : list int :=
  ([33; 40; 41; 42; 43; 44; 45; 46; 47; 51; 16; 6; 17; 3; 4; 5; 7; 8; 9; 11; 12; 13; 14; 23; 25; 31]
   ++ (if b then [27; 28] else []) ++ [0])%uint63.

(* the byte offset of AT_GID's value word, pair 21 *)
Definition GID_OFF : int := 344%uint63.

Definition aux_val (ph : int) (b : bool) (i : nat) : option sv :=
  match i with
  | 10%nat => Some (VP 7%uint63 (wp 0%uint63))
  | 11%nat => Some (VL (wp 4096%uint63))
  | 12%nat => Some (VL (wp 100%uint63))
  | 13%nat => Some (VL (wp 65600%uint63))
  | 14%nat => Some (VL (wp 56%uint63))
  | 15%nat => Some (VL (wp ph))
  | 16%nat | 17%nat | 23%nat => Some (VL (wp 0%uint63))
  | 19%nat | 20%nat => Some (VP 8%uint63 (wp 0%uint63))
  | 22%nat => Some (VBg false 3%uint63 (wp GID_OFF) 8%uint63)
  | 24%nat => Some (VP 6%uint63 (wp 0%uint63))
  | 26%nat => Some (VL (wp (if b then 28 else 0)%uint63))
  | 27%nat => if b then Some (VL (wp 32%uint63)) else None
  | 28%nat => if b then Some (VL (wp 0%uint63)) else None
  | _ => None
  end.

Definition cell1 (v : sv) : gran := Gran false [Cell 0%uint63 8%uint63 v].

Fixpoint aux_cells (ph : int) (b : bool) (ts : list int) (i : nat) : list (int * gran) :=
  match ts with
  | [] => []
  | t :: ts' =>
      (of_Z (Z.of_nat (2 * i)), cell1 (VL (wp t)))
      :: (match aux_val ph b i with Some v => [(of_Z (Z.of_nat (2 * i + 1)), cell1 v)] | None => [] end)
      ++ aux_cells ph b ts' (S i)
  end.

(* the start state's region 3 at flag [b], for an image of [ph] program headers *)
Definition R3Tbn (ph : int) (b : bool) : region :=
  Region 0%uint63 (VL (wp (if b then 464 else 432)%uint63)) false BGUnk (imap_of (aux_cells ph b (aux_types b) 0)).

Fixpoint dirty_from (g : int) (n : nat) (m : IMap.t gran) : IMap.t gran :=
  match n with O => m | S n' => dirty_from (PrimInt63.add g 1%uint63) n' (IMap.add g (Gran true []) m) end.

(* Region 3 as both flags have it: the 26 pairs before the CONFIG_RSEQ pairs, the same words at both
   values, and granules 52..57 (where AT_NULL sits at one value and the CONFIG_RSEQ pairs at the other)
   unknown.  The bound 432 is the smaller vector's size; a state of either value implies it. *)
Definition R3An (ph : int) : region :=
  Region 0%uint63 (VL (wp 432%uint63)) false BGUnk
    (dirty_from 52%uint63 6 (imap_of (List.filter (fun kv => PrimInt63.ltb (fst kv) 52%uint63) (aux_cells ph false (aux_types false) 0)))).

(* The two images' regions, each [R3Tbn] / [R3An] at its program-header count with the definition
   unfolded, so the region is itself a [Region] term. *)
Definition R3Tb (b : bool) : region := Eval cbv beta delta [R3Tbn] in R3Tbn 10%uint63 b.
Definition R3A : region := Eval cbv beta delta [R3An] in R3An 10%uint63.
Definition R3Tb_asan (b : bool) : region := Eval cbv beta delta [R3Tbn] in R3Tbn 11%uint63 b.
Definition R3A_asan : region := Eval cbv beta delta [R3An] in R3An 11%uint63.

End Auxv.
