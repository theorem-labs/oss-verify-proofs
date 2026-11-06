(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the placement premises of W_rom_place.v at the pinned placement PB_fr (W_img.v)
   and the sink head of image A (AE2k.v tfib_sink_head), in the form of W_w1_place.v.  The image's read-only bytes
   (in_rom) are its two non-writable segments, page-rounded as the image loader gives them: [0x10000, 0x30000) "r--"
   (ELF LOAD [0x10000, 0x2f994)) and [0x30000, 0x9d000) "r-x" (ELF LOAD [0x30994, 0x9c438)); g_s (0x5d88e0, 384
   bytes) and ofl_head (0x5f9b68, 8 bytes) are .bss, in the "rw-" segment [0x9f000, 0x5fb000).  str2_rom_fr: .str.2
   (0x20ee0, check_shape_ends' prefix) and the 8 bytes from it are in the "r--" segment (cshe_spec's PF clause). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YM05 YP0b YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_tbl W_kit W_journal W_rep W_img W_rom_place.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AE2k.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).

Lemma fr_rom_range : forall a, in_rom SEGS a -> 0x10000 <= a < 0x9d000.
Proof.
intros a (sg & Hin & Hw & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
  (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) frsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) frsegs sg Hin). }
rewrite Hw in H. clear Hin Hw.
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez. clear Eb Ez.
vm_compute in H. destruct H as [H|[H|[H|[H|[]]]]]; inversion H; subst; lia.
Qed.

Lemma g_s_rom_fr : forall a, VAL (A_OBJ 22) <= a < VAL (A_OBJ 22) + 384 -> ~ in_rom SEGS a.
Proof.
intros a Ha Hr. apply fr_rom_range in Hr.
let v := eval vm_compute in (VAL (A_OBJ 22)) in change (VAL (A_OBJ 22)) with v in Ha.
lia.
Qed.

Lemma ofl_head_rom_fr : forall a, in_rom SEGS a ->
~ (AOFL_HEAD (SK := AE2k.tfib_sink_head) <= a < AOFL_HEAD (SK := AE2k.tfib_sink_head) + 8).
Proof.
intros a Hr. apply fr_rom_range in Hr. cbn [AOFL_HEAD YI16.sk_ofl_head AE2k.tfib_sink_head].
unfold AE2k.A_ofl_head. lia.
Qed.

Lemma cnl_g_rom_out_fr : forall (B : asyms) HA (j : nat), HA = VAL (A_OBJ 22) + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a)) ->
rom_out (SK := AE2k.tfib_sink_head) SEGS B [(HA + 80, 16)].
Proof.
intros B HA j EHA Hj HNS.
exact (cnl_g_rom_out (SK := AE2k.tfib_sink_head) (PI := PB_fr) B HA j EHA Hj g_s_rom_fr ofl_head_rom_fr HNS).
Qed.

(* the image's "r--" segment [0x10000, 0x30000) is read-only *)
Lemma fr_rom000 : forall a, 0x10000 <= a < 0x30000 -> in_rom SEGS a.
Proof.
intros a Ha. exists Asan.Asan_segment_000. split; [left; reflexivity|]. split; [vm_compute; reflexivity|].
change (Z.of_N (seg_base Asan.Asan_segment_000)) with 0x10000.
change (Z.of_N (seg_size Asan.Asan_segment_000)) with 0x20000. lia.
Qed.
(* .str.2 (check_shape_ends' prefix PF, 0x20ee0) and the 8 bytes strlen's word read may touch are read-only *)
Lemma str2_rom_fr : forall a, VAL (A_OBJ 28) <= a < VAL (A_OBJ 28) + 8 -> in_rom SEGS a.
Proof.
intros a Ha. apply fr_rom000.
let v := eval vm_compute in (VAL (A_OBJ 28)) in change (VAL (A_OBJ 28)) with v in Ha.
lia.
Qed.
End a.
