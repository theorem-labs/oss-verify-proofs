(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List String.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.K5.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive lkind : Type := LK_s | LK_d | LK_zu.

Definition LF_00 : list Z := str "Error in %s: %s" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_01 : list Z := str "Error in %s: requested w = %d, h = %d, d = %d" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_02 : list Z := str "Error in %s: fuzzer requested > 64 MB; refused" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_03 : list Z := str "Error in %s: fuzzer requested width > 20K; refused" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_04 : list Z := str "Error in %s: fuzzer requested height > 20K; refused" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_05 : list Z := str "Warning in %s: ptr address is null!" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_06 : list Z := str "Warning in %s: ptr address is null!" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_07 : list Z := str "Info in %s: pix is 24 bpp" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_08 : list Z := str "Error in %s: invalid cmap depth: %d" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_09 : list Z := str "Error in %s: invalid cmap nalloc = %d; d = %d" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_10 : list Z := str "Error in %s: invalid cmap n: %d; nalloc = %d" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_11 : list Z := str "Error in %s: pix depth %d > 8" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_12 : list Z := str "Error in %s: (pix depth = %d) > (cmap depth = %d)" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_13 : list Z := str "Error in %s: cmap array is empty; invalid with any pix" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_14 : list Z := str "Error in %s: cmap entries = %d > max colors for pix = %d" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_15 : list Z := str "Error in %s: (max index in image = %d) >= (number entries in colormap = %d)" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_16 : list Z := str "Error in %s: invalid nbytes = %zu" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_17 : list Z := str "Error in %s: pixdata_size = %d, memdata_size = %d, imdata_size = %d not all equal!" ++ [10; 0].   (* [comment removed for export] *)

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
  ; (LF_17, [LK_s; LK_d; LK_d; LK_d]) ].

(* [comment removed for export] *)
Definition LEPT_FMT_TAB_A16 : list (Z * list Z * list lkind) :=
  [ (0x22aa0, LF_00, [LK_s; LK_s])
  ; (0x22ce0, LF_01, [LK_s; LK_d; LK_d; LK_d])
  ; (0x22da0, LF_02, [LK_s])
  ; (0x22e00, LF_03, [LK_s])
  ; (0x22e60, LF_04, [LK_s])
  ; (0x22ec0, LF_05, [LK_s])
  ; (0x23280, LF_06, [LK_s])
  ; (0x23140, LF_07, [LK_s])
  ; (0x233e0, LF_08, [LK_s; LK_d])
  ; (0x23440, LF_09, [LK_s; LK_d; LK_d])
  ; (0x234a0, LF_10, [LK_s; LK_d; LK_d])
  ; (0x23500, LF_11, [LK_s; LK_d])
  ; (0x23540, LF_12, [LK_s; LK_d; LK_d])
  ; (0x235a0, LF_13, [LK_s])
  ; (0x23600, LF_14, [LK_s; LK_d; LK_d])
  ; (0x23660, LF_15, [LK_s; LK_d; LK_d])
  ; (0x23c00, LF_16, [LK_s; LK_zu])
  ; (0x23d60, LF_17, [LK_s; LK_d; LK_d; LK_d]) ].
