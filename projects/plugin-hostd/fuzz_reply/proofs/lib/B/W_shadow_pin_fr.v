(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_reply.asan-ubsan) instance lemmas of W_shadow_pin.v's ashp, at
   B's pinned placement PB_fr (lib/B/W_img.v), for every B with B's start-up instance TfibSyms B (lib/B/YF0m.v).
   Written for image B, NOT generated from lib/A/W_shadow_pin_fr.v: every address and shadow byte below is read from
   B's own tables.  Each lemma is shp_ashp over B's Tfib_const_shadow and Tfib_zero_shadow, decided by vm_compute.
   The literals (lib/B/W_place.v fr_obj; the A_OBJ indices differ from image A's) and the shadow bytes their last
   granule rests on (lib/B/YF0m.v Tfib_const_shadow :487-515, Tfib_zero_shadow :818):
     .str.2   ""                A_OBJ 25 = 0x20ee0, 1 byte   granule 0x20ee0 shadow 0x7fffc1dc = 1
     .str.4   " end\0"          A_OBJ 28 = 0x20f00, 5 bytes  granule 0x20f00 shadow 0x7fffc1e0 = 5
     .str.5   "param_gesture\0" A_OBJ 18 = 0x20f20, 14       granule 0x20f20 zero (Tfib_zero_shadow (0x20f20, 8)),
                                                             granule 0x20f28 shadow 0x7fffc1e5 = 6
     .str.6   "begin\0"         A_OBJ 20 = 0x20f40, 6 bytes  granule 0x20f40 shadow 0x7fffc1e8 = 6
     .str.7   "end\0"           A_OBJ 21 = 0x20f60, 4 bytes  granule 0x20f60 shadow 0x7fffc1ec = 4
   Every other byte of each 8-aligned shadow hull is a 0xf9 redzone cell of B's Tfib_const_shadow or the zero shadow
   byte 0x7fffc1e4.  The names carry the byte count: ashp_<literal>_<n>_fr.  str2_rom_fr: .str.2 and the 8 bytes
   from it lie in B's "r--" segment [0x10000, 0x30000) (cshe_spec's PF clause). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YM05 YP0b YA0n YG00 YG0a YG01 YG0f YG0n YG0d YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_tbl W_kit W_img W_contract W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YF0l YF0m.
From OSSVerify.plugin_hostd.fuzz_reply.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis HT : YF0m.TfibSyms B.

Lemma tfib_shp : forall a n, shp_check YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow a n = true ->
ashp (PI := PB_fr) B a n.
Proof.
intros a n H. apply (shp_ashp B YF0m.Tfib_const_shadow YF0m.Tfib_zero_shadow); [| | exact H].
- intros ly c Hc. rewrite (YF0m.ts_const _ HT ly). unfold YF0m.Tfib_const.
  apply in_or_app. right. apply in_or_app. right. exact Hc.
- intros r Hr. rewrite (YF0m.ts_zsh _ HT). exact Hr.
Qed.

(* .str.2 "" (check_shape_ends' prefix, PF), A_OBJ 25 = 0x20ee0, 1 byte; 0x7fffc1dc = 1 *)
Lemma ashp_str2_1_fr : ashp (PI := PB_fr) B (VAL (A_OBJ 25)) 1.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.4 " end" (check_shape_ends' loop 3 bcmp operand), A_OBJ 28 = 0x20f00, 4 bytes; 0x7fffc1e0 = 5 *)
Lemma ashp_end5_4_fr : ashp (PI := PB_fr) B (VAL A_lit_end5) 4.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.4 " end\0", A_OBJ 28 = 0x20f00, 5 bytes; 0x7fffc1e0 = 5 *)
Lemma ashp_end5_5_fr : ashp (PI := PB_fr) B (VAL A_lit_end5) 5.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.5 "param_gesture", A_OBJ 18 = 0x20f20, 13 bytes; 0x7fffc1e4 = 0 (zero shadow), 0x7fffc1e5 = 6 *)
Lemma ashp_gesture_13_fr : ashp (PI := PB_fr) B (VAL A_lit_gesture) 13.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.5 "param_gesture\0", A_OBJ 18 = 0x20f20, 14 bytes; 0x7fffc1e4 = 0 (zero shadow), 0x7fffc1e5 = 6 *)
Lemma ashp_gesture_14_fr : ashp (PI := PB_fr) B (VAL A_lit_gesture) 14.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.6 "begin", A_OBJ 20 = 0x20f40, 5 bytes; 0x7fffc1e8 = 6 *)
Lemma ashp_begin_5_fr : ashp (PI := PB_fr) B (VAL A_lit_begin) 5.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.6 "begin\0", A_OBJ 20 = 0x20f40, 6 bytes; 0x7fffc1e8 = 6 *)
Lemma ashp_begin_6_fr : ashp (PI := PB_fr) B (VAL A_lit_begin) 6.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.7 "end", A_OBJ 21 = 0x20f60, 3 bytes; 0x7fffc1ec = 4 *)
Lemma ashp_end_3_fr : ashp (PI := PB_fr) B (VAL A_lit_end) 3.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* .str.7 "end\0", A_OBJ 21 = 0x20f60, 4 bytes; 0x7fffc1ec = 4 *)
Lemma ashp_end_4_fr : ashp (PI := PB_fr) B (VAL A_lit_end) 4.
Proof. apply tfib_shp. vm_compute. reflexivity. Qed.
(* The address each lemma is about, checked on image B's placement (a wrong object index fails here). *)
Example ashp_fr_addrs :
  VAL (A_OBJ 25) = 0x20ee0 /\ VAL A_lit_end5 = 0x20f00 /\ VAL A_lit_gesture = 0x20f20 /\
  VAL A_lit_begin = 0x20f40 /\ VAL A_lit_end = 0x20f60.
Proof. vm_compute. repeat split; reflexivity. Qed.
End a.

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
(* B's "r--" segment [0x10000, 0x30000) is read-only *)
Lemma fr_rom000 : forall a, 0x10000 <= a < 0x30000 -> in_rom SEGS a.
Proof.
intros a Ha. exists AsanUbsan.AsanUbsan_segment_000. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
change (Z.of_N (seg_base AsanUbsan.AsanUbsan_segment_000)) with 0x10000.
change (Z.of_N (seg_size AsanUbsan.AsanUbsan_segment_000)) with 0x20000. lia.
Qed.
(* .str.2 (A_OBJ 25 = 0x20ee0) and the 8 bytes strlen's word read may touch are read-only *)
Lemma str2_rom_fr : forall a, VAL (A_OBJ 25) <= a < VAL (A_OBJ 25) + 8 -> in_rom SEGS a.
Proof.
intros a Ha. apply fr_rom000.
let v := eval vm_compute in (VAL (A_OBJ 25)) in change (VAL (A_OBJ 25)) with v in Ha.
lia.
Qed.
End r.
