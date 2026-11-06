(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List String.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.G3 Require Export LeptFormats.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LF_18 : list Z := str "Warning in %s: no mask; nothing to do" ++ [10; 0].   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LEPT_FMT_LIST : list (list Z * list lkind) :=
  [ (LF_00, [LK_s; LK_s])
  ; (LF_01, [LK_s; LK_d; LK_d; LK_d])
  ; (LF_02, [LK_s])
  ; (LF_03, [LK_s])
  ; (LF_04, [LK_s])
  ; (LF_05, [LK_s])
  ; (LF_06, [LK_s])
  ; (LF_07, [LK_s])
  ; (LF_08, [LK_s; LK_d])
  ; (LF_09, [LK_s; LK_d; LK_d])
  ; (LF_10, [LK_s; LK_d; LK_d])
  ; (LF_11, [LK_s; LK_d])
  ; (LF_12, [LK_s; LK_d; LK_d])
  ; (LF_13, [LK_s])
  ; (LF_14, [LK_s; LK_d; LK_d])
  ; (LF_15, [LK_s; LK_d; LK_d])
  ; (LF_16, [LK_s; LK_zu])
  ; (LF_17, [LK_s; LK_d; LK_d; LK_d])
  ; (LF_18, [LK_s]) ].

Lemma LEPT_FMT_LIST_ext : LEPT_FMT_LIST = G3.LeptFormats.LEPT_FMT_LIST ++ [ (LF_18, [LK_s]) ].
Proof. reflexivity. Qed.
