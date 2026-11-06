(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3 Require Export LeptFormats LeptShapes.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3pm Require Export LeptFormatsPm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LS_18 : list Z * pshape := ([87; 97; 114; 110; 105; 110; 103; 32; 105; 110; 32], [(LK_s, 58, [32; 110; 111; 32; 109; 97; 115; 107; 59; 32; 110; 111; 116; 104; 105; 110; 103; 32; 116; 111; 32; 100; 111; 10])]).

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
  ; (LF_17, map (fun it => fst (fst it)) (snd LS_17), LS_17)
  ; (LF_18, map (fun it => fst (fst it)) (snd LS_18), LS_18) ].

Lemma LEPT_SHAPES_ext : LEPT_SHAPES = G3.LeptShapes.LEPT_SHAPES ++ [ (LF_18, map (fun it => fst (fst it)) (snd LS_18), LS_18) ].
Proof. reflexivity. Qed.

Lemma LEPT_SHAPES_ok : forallb shape_row_ok LEPT_SHAPES = true.
Proof. vm_compute. reflexivity. Qed.

Lemma LEPT_SHAPES_cover : map (fun e => fst e) LEPT_SHAPES = LEPT_FMT_LIST.
Proof. vm_compute. reflexivity. Qed.
