(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.G3 Require Import LeptFormats.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition pshape : Type := list (lkind * Z * list Z).

Definition lkind_bytes (k : lkind) : list Z :=
  match k with LK_s => [37; 115] | LK_d => [37; 100] | LK_zu => [37; 122; 117] end.

Fixpoint pshape_bytes (sh : pshape) : list Z :=
  match sh with
  | [] => []
  | (k, nx, t) :: r => lkind_bytes k ++ nx :: t ++ pshape_bytes r
  end.

(* [comment removed for export] *)
Definition ptxt_ok (l : list Z) : bool := forallb (fun c => (0 <? c) && (c <? 256) && negb (c =? 37)) l.
Definition pshape_ok (sh : pshape) : bool := forallb (fun it => ptxt_ok (snd (fst it) :: snd it)) sh.

Definition LS_00 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32]); (LK_s, 10, [])]).
Definition LS_01 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 119; 32; 61; 32]); (LK_d, 44, [32; 104; 32; 61; 32]); (LK_d, 44, [32; 100; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_02 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 102; 117; 122; 122; 101; 114; 32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 62; 32; 54; 52; 32; 77; 66; 59; 32; 114; 101; 102; 117; 115; 101; 100; 10])]).
Definition LS_03 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 102; 117; 122; 122; 101; 114; 32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 119; 105; 100; 116; 104; 32; 62; 32; 50; 48; 75; 59; 32; 114; 101; 102; 117; 115; 101; 100; 10])]).
Definition LS_04 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 102; 117; 122; 122; 101; 114; 32; 114; 101; 113; 117; 101; 115; 116; 101; 100; 32; 104; 101; 105; 103; 104; 116; 32; 62; 32; 50; 48; 75; 59; 32; 114; 101; 102; 117; 115; 101; 100; 10])]).
Definition LS_05 : list Z * pshape := ([87; 97; 114; 110; 105; 110; 103; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 116; 114; 32; 97; 100; 100; 114; 101; 115; 115; 32; 105; 115; 32; 110; 117; 108; 108; 33; 10])]).
Definition LS_06 : list Z * pshape := ([87; 97; 114; 110; 105; 110; 103; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 116; 114; 32; 97; 100; 100; 114; 101; 115; 115; 32; 105; 115; 32; 110; 117; 108; 108; 33; 10])]).
Definition LS_07 : list Z * pshape := ([73; 110; 102; 111; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 105; 120; 32; 105; 115; 32; 50; 52; 32; 98; 112; 112; 10])]).
Definition LS_08 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 99; 109; 97; 112; 32; 100; 101; 112; 116; 104; 58; 32]); (LK_d, 10, [])]).
Definition LS_09 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 99; 109; 97; 112; 32; 110; 97; 108; 108; 111; 99; 32; 61; 32]); (LK_d, 59, [32; 100; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_10 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 99; 109; 97; 112; 32; 110; 58; 32]); (LK_d, 59, [32; 110; 97; 108; 108; 111; 99; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_11 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 105; 120; 32; 100; 101; 112; 116; 104; 32]); (LK_d, 32, [62; 32; 56; 10])]).
Definition LS_12 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 40; 112; 105; 120; 32; 100; 101; 112; 116; 104; 32; 61; 32]); (LK_d, 41, [32; 62; 32; 40; 99; 109; 97; 112; 32; 100; 101; 112; 116; 104; 32; 61; 32]); (LK_d, 41, [10])]).
Definition LS_13 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 99; 109; 97; 112; 32; 97; 114; 114; 97; 121; 32; 105; 115; 32; 101; 109; 112; 116; 121; 59; 32; 105; 110; 118; 97; 108; 105; 100; 32; 119; 105; 116; 104; 32; 97; 110; 121; 32; 112; 105; 120; 10])]).
Definition LS_14 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 99; 109; 97; 112; 32; 101; 110; 116; 114; 105; 101; 115; 32; 61; 32]); (LK_d, 32, [62; 32; 109; 97; 120; 32; 99; 111; 108; 111; 114; 115; 32; 102; 111; 114; 32; 112; 105; 120; 32; 61; 32]); (LK_d, 10, [])]).
Definition LS_15 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 40; 109; 97; 120; 32; 105; 110; 100; 101; 120; 32; 105; 110; 32; 105; 109; 97; 103; 101; 32; 61; 32]); (LK_d, 41, [32; 62; 61; 32; 40; 110; 117; 109; 98; 101; 114; 32; 101; 110; 116; 114; 105; 101; 115; 32; 105; 110; 32; 99; 111; 108; 111; 114; 109; 97; 112; 32; 61; 32]); (LK_d, 41, [10])]).
Definition LS_16 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 105; 110; 118; 97; 108; 105; 100; 32; 110; 98; 121; 116; 101; 115; 32; 61; 32]); (LK_zu, 10, [])]).
Definition LS_17 : list Z * pshape := ([69; 114; 114; 111; 114; 32; 105; 110; 32], [(LK_s, 58, [32; 112; 105; 120; 100; 97; 116; 97; 95; 115; 105; 122; 101; 32; 61; 32]); (LK_d, 44, [32; 109; 101; 109; 100; 97; 116; 97; 95; 115; 105; 122; 101; 32; 61; 32]); (LK_d, 44, [32; 105; 109; 100; 97; 116; 97; 95; 115; 105; 122; 101; 32; 61; 32]); (LK_d, 32, [110; 111; 116; 32; 97; 108; 108; 32; 101; 113; 117; 97; 108; 33; 10])]).

Definition LEPT_SHAPES : list (list Z * list lkind * (list Z * pshape)) :=
  [ (LF_00, map (fun it => fst (fst it)) (snd LS_00), LS_00)
  ; (LF_01, map (fun it => fst (fst it)) (snd LS_01), LS_01)
  ; (LF_02, map (fun it => fst (fst it)) (snd LS_02), LS_02)
  ; (LF_03, map (fun it => fst (fst it)) (snd LS_03), LS_03)
  ; (LF_04, map (fun it => fst (fst it)) (snd LS_04), LS_04)
  ; (LF_05, map (fun it => fst (fst it)) (snd LS_05), LS_05)
  ; (LF_06, map (fun it => fst (fst it)) (snd LS_06), LS_06)
  ; (LF_07, map (fun it => fst (fst it)) (snd LS_07), LS_07)
  ; (LF_08, map (fun it => fst (fst it)) (snd LS_08), LS_08)
  ; (LF_09, map (fun it => fst (fst it)) (snd LS_09), LS_09)
  ; (LF_10, map (fun it => fst (fst it)) (snd LS_10), LS_10)
  ; (LF_11, map (fun it => fst (fst it)) (snd LS_11), LS_11)
  ; (LF_12, map (fun it => fst (fst it)) (snd LS_12), LS_12)
  ; (LF_13, map (fun it => fst (fst it)) (snd LS_13), LS_13)
  ; (LF_14, map (fun it => fst (fst it)) (snd LS_14), LS_14)
  ; (LF_15, map (fun it => fst (fst it)) (snd LS_15), LS_15)
  ; (LF_16, map (fun it => fst (fst it)) (snd LS_16), LS_16)
  ; (LF_17, map (fun it => fst (fst it)) (snd LS_17), LS_17) ].

(* [comment removed for export] *)
Definition shape_row_ok (e : list Z * list lkind * (list Z * pshape)) : bool :=
  let '(f, ks, (t0, sh)) := e in
  (if list_eq_dec Z.eq_dec f (t0 ++ pshape_bytes sh ++ [0]) then true else false)
  && ptxt_ok t0 && pshape_ok sh && (1 <=? Z.of_nat (length (t0 ++ pshape_bytes sh))).

Lemma LEPT_SHAPES_ok : forallb shape_row_ok LEPT_SHAPES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma LEPT_SHAPES_cover : map (fun e => fst e) LEPT_SHAPES = LEPT_FMT_LIST.
Proof. vm_compute. reflexivity. Qed.
