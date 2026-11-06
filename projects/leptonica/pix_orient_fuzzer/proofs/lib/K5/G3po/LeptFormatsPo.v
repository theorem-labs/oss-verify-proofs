(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List String.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.G3 Require Export LeptFormats.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptFormatsPo () := "I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00I69OSSVerify5KrLib2K52G3;LeptFormats5lkind00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K52G3;LeptFormats=LEPT_FMT_LISTC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3po=LeptFormatsPo5LF_18C1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K52G3;LeptFormats5lkind01C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3po=LeptFormatsPo5LF_19C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3po=LeptFormatsPo5LF_20C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3po=LeptFormatsPo5LF_21C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3po=LeptFormatsPo5LF_22C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K54G3po=LeptFormatsPo5LF_23C1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LF_18 : list Z := str "Info in %s: text orientation not determined; no rotation" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_19 : list Z := str "Info in %s: text is oriented up; no rotation" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_20 : list Z := str "Info in %s: landscape; text oriented left; 90 cw rotation" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_21 : list Z := str "Info in %s: text oriented down; 180 cw rotation" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_22 : list Z := str "Info in %s: landscape; text oriented right; 270 cw rotation" ++ [10; 0].   (* [comment removed for export] *)
Definition LF_23 : list Z := str "Info in %s: not enough confidence to get orientation" ++ [10; 0].   (* [comment removed for export] *)

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
  ; (LF_18, [LK_s])
  ; (LF_19, [LK_s])
  ; (LF_20, [LK_s])
  ; (LF_21, [LK_s])
  ; (LF_22, [LK_s])
  ; (LF_23, [LK_s]) ].

Lemma LEPT_FMT_LIST_ext : LEPT_FMT_LIST = G3.LeptFormats.LEPT_FMT_LIST ++ [ (LF_18, [LK_s]); (LF_19, [LK_s]); (LF_20, [LK_s]); (LF_21, [LK_s]); (LF_22, [LK_s]); (LF_23, [LK_s]) ].
Proof.
ltac2:(KReplay.run1 (kr_t_LeptFormatsPo ()) [] "p;1p;2p;3p;4g0000j12Tg000Pj26Tg0010j13Tg001Pj30Tg0020j41Tg002Pj35Tg002mj24Tg003G#2R0g003eR1#2R2'6R3#2g004cP0P2g005gg006g%31501R1C1P0P2g007eP1C1P0P2g008eP1C1P0P2g009eP1C1P0P2g00:eP1C1P0P2g00;eP1C1%33503503503503503503553'4o"). Qed.
