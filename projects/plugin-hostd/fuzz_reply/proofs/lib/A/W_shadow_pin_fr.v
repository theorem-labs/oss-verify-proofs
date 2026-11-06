(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: W_shadow_pin.v's ashp for the program's literals at the pinned placement PB_fr
   (W_img.v), for every B with the start-up instance's TfibSyms B (lib/A/AF0m.v, sha256 3845e3de2622; internal record, carried by path
   as in a working branch 56c6b16d1c8).  Each lemma is shp_ashp over Tfib_const_shadow and
   Tfib_zero_shadow, decided by vm_compute.  The literals and the shadow bytes their last granule rests on (a
   partial granule, so no zero-shadow range holds the literal and `azs` is false there):
     .str.2   ""             0x20ee0, 1 byte    granule 0x20ee0 shadow 0x7fffc1dc = 1
     .str.4   " end\0"       0x20f00, 5 bytes   granule 0x20f00 shadow 0x7fffc1e0 = 5
     .str.5   "param_gesture\0" 0x20f20, 14     granule 0x20f20 zero (Tfib_zero_shadow (0x20f20, 8)),
                                                granule 0x20f28 shadow 0x7fffc1e5 = 6
     .str.6   "begin\0"      0x20f40, 6 bytes   granule 0x20f40 shadow 0x7fffc1e8 = 6
     .str.7   "end\0"        0x20f60, 4 bytes   granule 0x20f60 shadow 0x7fffc1ec = 4
   Every other byte of each 8-aligned shadow hull is a 0xf9 redzone cell of Tfib_const_shadow or the zero shadow
   byte 0x7fffc1e4.  The names carry the byte count: ashp_<literal>_<n>_fr. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_kit W_img W_contract W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AF0l AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis HT : AF0m.TfibSyms B.

Lemma tfib_shp : forall a n, shp_check AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow a n = true ->
ashp (PI := PB_fr) B a n.
Proof.
intros a n H. apply (shp_ashp B AF0m.Tfib_const_shadow AF0m.Tfib_zero_shadow); [| | exact H].
- intros ly c Hc. rewrite (AF0m.ts_const _ HT ly). unfold AF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right. exact Hc.
- intros r Hr. rewrite (AF0m.ts_zsh _ HT). exact Hr.
Qed.

(* .str.2 "" (check_shape_ends' prefix, PF), 0x20ee0, 1 byte; 0x7fffc1dc = 1 *)
Lemma ashp_str2_1_fr : ashp (PI := PB_fr) B (VAL (A_OBJ 28)) 1.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.4 " end" (check_shape_ends' loop 3 bcmp operand), 0x20f00, 4 bytes; 0x7fffc1e0 = 5 *)
Lemma ashp_end5_4_fr : ashp (PI := PB_fr) B (VAL A_lit_end5) 4.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.4 " end\0", 0x20f00, 5 bytes; 0x7fffc1e0 = 5 *)
Lemma ashp_end5_5_fr : ashp (PI := PB_fr) B (VAL A_lit_end5) 5.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.5 "param_gesture", 0x20f20, 13 bytes; 0x7fffc1e4 = 0 (zero shadow), 0x7fffc1e5 = 6 *)
Lemma ashp_gesture_13_fr : ashp (PI := PB_fr) B (VAL A_lit_gesture) 13.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.5 "param_gesture\0", 0x20f20, 14 bytes; 0x7fffc1e4 = 0 (zero shadow), 0x7fffc1e5 = 6 *)
Lemma ashp_gesture_14_fr : ashp (PI := PB_fr) B (VAL A_lit_gesture) 14.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.6 "begin", 0x20f40, 5 bytes; 0x7fffc1e8 = 6 *)
Lemma ashp_begin_5_fr : ashp (PI := PB_fr) B (VAL A_lit_begin) 5.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.6 "begin\0", 0x20f40, 6 bytes; 0x7fffc1e8 = 6 *)
Lemma ashp_begin_6_fr : ashp (PI := PB_fr) B (VAL A_lit_begin) 6.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.7 "end", 0x20f60, 3 bytes; 0x7fffc1ec = 4 *)
Lemma ashp_end_3_fr : ashp (PI := PB_fr) B (VAL A_lit_end) 3.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.7 "end\0", 0x20f60, 4 bytes; 0x7fffc1ec = 4 *)
Lemma ashp_end_4_fr : ashp (PI := PB_fr) B (VAL A_lit_end) 4.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
End a.
