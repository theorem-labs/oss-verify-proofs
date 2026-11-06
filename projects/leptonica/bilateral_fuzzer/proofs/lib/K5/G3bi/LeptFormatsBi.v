(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List String.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.G3 Require Export LeptFormats.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptFormatsBi () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2eq01I69OSSVerify5KrLib2K52G3;LeptFormats5lkind00C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52G3;LeptFormats5lkind02C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00C69OSSVerify5KrLib2K52G3;LeptFormats=LEPT_FMT_LISTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3bi=LeptFormatsBi5LF_18C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52G3;LeptFormats5lkind01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3bi=LeptFormatsBi5LF_19C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LF_18 : list Z := str "Warning in %s: w = %d, h = %d; w or h < 2 * filtersize = %d; returning copy" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_19 : list Z := str "Warning in %s: w = %d < 2 * sx + 1 = %d, or h = %d < 2 * sy + 1 = %d; returning copy" ++ [10; 0].   (* [comment removed for export] *)

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
  ; (LF_18, [LK_s; LK_d; LK_d; LK_d])
  ; (LF_19, [LK_s; LK_d; LK_d; LK_d; LK_d]) ].

Lemma LEPT_FMT_LIST_ext : LEPT_FMT_LIST = G3.LeptFormats.LEPT_FMT_LIST ++ [ (LF_18, [LK_s; LK_d; LK_d; LK_d]); (LF_19, [LK_s; LK_d; LK_d; LK_d; LK_d]) ].
Proof.
ltac2:(KReplay.run1 (kr_t_LeptFormatsBi ()) [] "p;1p;2p;3p;4g0000j12Tg000Pj27Tg0010j13Tg001Pj30Tg0020j44Tg002Pj36Tg002mj25Tg003GR0g004Ef030p=1g005C#2R1%20R2'7R3#2g005aP1P2g006eg007eR4%30#1#1#1R5500C4P1P2g008c%159004C4%33503503563'5o"). Qed.
