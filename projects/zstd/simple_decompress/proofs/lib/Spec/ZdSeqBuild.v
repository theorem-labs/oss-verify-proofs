(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fse_tablestep (size : Z) : Z := size / 2 + size / 8 + 3.

(* [comment removed for export] *)
Fixpoint set_base_nat (n : nat) (v : Z) (l : list seqsym) : list seqsym :=
  match l, n with
  | [], _ => []
  | c :: t, O => mkSS (ss_next c) (ss_nbAdd c) (ss_nbBits c) v :: t
  | c :: t, S n' => c :: set_base_nat n' v t
  end.
Definition set_base (i v : Z) (l : list seqsym) : list seqsym := if i <? 0 then l else set_base_nat (Z.to_nat i) v l.

Fixpoint set_cell_nat (n : nat) (c' : seqsym) (l : list seqsym) : list seqsym :=
  match l, n with
  | [], _ => []
  | _ :: t, O => c' :: t
  | c :: t, S n' => c :: set_cell_nat n' c' t
  end.
Definition set_cell (i : Z) (c' : seqsym) (l : list seqsym) : list seqsym := if i <? 0 then l else set_cell_nat (Z.to_nat i) c' l.

Definition cell_nth (l : list seqsym) (i : Z) : seqsym := nth (Z.to_nat i) l ss0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lowprob (fuel : nat) (norm : list Z) (largeLimit : Z) (s : Z)
                 (cells : list seqsym) (symNext : list Z) (high fast : Z) : list seqsym * list Z * Z * Z :=
  match fuel with
  | O => (cells, symNext, high, fast)
  | S f =>
    let n := Znth s norm in
    if n =? -1 then lowprob f norm largeLimit (s + 1) (set_base high s cells) (Zupd s 1 symNext) (high - 1) fast
    else lowprob f norm largeLimit (s + 1) cells (Zupd s (n mod 2^16) symNext) high (if largeLimit <=? n then 0 else fast)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition write8 (spread : list Z) (p s : Z) : list Z :=
  Zupd (p + 7) s (Zupd (p + 6) s (Zupd (p + 5) s (Zupd (p + 4) s (Zupd (p + 3) s (Zupd (p + 2) s (Zupd (p + 1) s (Zupd p s spread))))))).

Fixpoint lay_more (fuel : nat) (spread : list Z) (pos s i n : Z) : list Z :=
  match fuel with
  | O => spread
  | S f => if i <? n then lay_more f (write8 spread (pos + i) s) pos s (i + 8) n else spread
  end.

Fixpoint lay_symbols (fuel : nat) (norm : list Z) (s pos : Z) (spread : list Z) : list Z * Z :=
  match fuel with
  | O => (spread, pos)
  | S f =>
    let n := Znth s norm in
    lay_symbols f norm (s + 1) (pos + n) (lay_more (Z.to_nat (n / 8 + 1)) (write8 spread pos s) pos s 8 n)
  end.

(* [comment removed for export] *)
Fixpoint place_fast (fuel : nat) (size step : Z) (spread : list Z) (s position : Z) (cells : list seqsym) : list seqsym * Z :=
  match fuel with
  | O => (cells, position)
  | S f =>
    let c1 := set_base (position mod size) (Znth s spread) cells in
    let c2 := set_base ((position + step) mod size) (Znth (s + 1) spread) c1 in
    place_fast f size step spread (s + 2) ((position + 2 * step) mod size) c2
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint skip_low (fuel : nat) (size step high position : Z) : Z :=
  match fuel with
  | O => position
  | S f => if high <? position then skip_low f size step high ((position + step) mod size) else position
  end.

(* [comment removed for export] *)
Definition next_pos (size step high position : Z) : Z :=
  skip_low (Z.to_nat size) size step high ((position + step) mod size).

Fixpoint place_n (k : nat) (size step high s position : Z) (cells : list seqsym) : list seqsym * Z :=
  match k with
  | O => (cells, position)
  | S k' => place_n k' size step high s (next_pos size step high position) (set_base position s cells)
  end.

Fixpoint spread_slow (fuel : nat) (norm : list Z) (size step high s position : Z) (cells : list seqsym) : list seqsym * Z :=
  match fuel with
  | O => (cells, position)
  | S f =>
    let '(cells', position') := place_n (Z.to_nat (Znth s norm)) size step high s position cells in
    spread_slow f norm size step high (s + 1) position' cells'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition build_one (tl : Z) (base bits : list Z) (symbol ns : Z) : seqsym :=
  let nbBits := (tl - Z.log2 ns) mod 256 in
  mkSS ((ns * 2^nbBits - 2^tl) mod 2^16) (Znth symbol bits) nbBits (Znth symbol base).

Fixpoint build_cells (fuel : nat) (tl : Z) (base bits : list Z) (u : Z) (cells : list seqsym) (symNext : list Z)
  : list seqsym * list Z :=
  match fuel with
  | O => (cells, symNext)
  | S f =>
    let symbol := ss_base (cell_nth cells u) in
    let ns := Znth symbol symNext in
    build_cells f tl base bits (u + 1) (set_cell u (build_one tl base bits symbol ns) cells) (Zupd symbol ((ns + 1) mod 2^16) symNext)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition build_fse_table (base bits : list Z) (norm : list Z) (maxSV tl : Z)
                           (cells0 : list seqsym) (symNext0 spread0 : list Z) : seq_table * list Z * list Z :=
  let size := 2^tl in
  let step := fse_tablestep size in
  let maxSV1 := Z.to_nat (maxSV + 1) in
  let '(cells1, symNext1, high, fast) := lowprob maxSV1 norm (2^(tl - 1)) 0 cells0 symNext0 (size - 1) 1 in
  let '(cells2, spread2) :=
    if high =? size - 1 then
      let '(spread1, _) := lay_symbols maxSV1 norm 0 0 spread0 in
      (fst (place_fast (Z.to_nat (size / 2)) size step spread1 0 0 cells1), spread1)
    else (fst (spread_slow maxSV1 norm size step high 0 0 cells1), spread0) in
  let '(cells3, symNext3) := build_cells (Z.to_nat size) tl base bits 0 cells2 symNext1 in
  (mkST fast tl cells3, symNext3, spread2).

Definition build_fse_table_k (k : seq_kind) := build_fse_table (kind_base k) (kind_bits k).
