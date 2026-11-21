(* reloc-zl14tag tagged blocks: asan 1 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import
  Tgt_zlib_uncompress_fuzzer_asan TgtO_zlib_uncompress_fuzzer_both.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import AsanAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Notation Src_0_loaded_segments := Src_zlib_zlib_uncompress_fuzzer_repro_loaded_segments.
Definition Src_0_top : Z := 0x94000%Z.
Lemma Src_0_wx_nowrap : wx_segs_nowrap Src_0_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Src_0_segs_below : segs_below_b Src_0_loaded_segments Src_0_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Src_0_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Src_0_top <= bv_unsigned a)%Z) ->
  H_off_segments Src_0_loaded_segments H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Src_0_segs_below Ha). Qed.
Lemma Src_0_H_off_mkH : forall L A,
  ranges_from_b L Src_0_top = true -> H_off_segments Src_0_loaded_segments (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Src_0_segs_below HL). Qed.

(* [comment removed for export] *)
Definition Asan_top : Z := 0x67e040%Z.
Lemma Asan_wx_nowrap : wx_segs_nowrap Tgt_zlib_uncompress_fuzzer_asan_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan_segs_below : segs_below_b Tgt_zlib_uncompress_fuzzer_asan_loaded_segments Asan_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Asan_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Asan_top <= bv_unsigned a)%Z) ->
  H_off_segments Tgt_zlib_uncompress_fuzzer_asan_loaded_segments H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan_segs_below Ha). Qed.
Lemma Asan_H_off_mkH : forall L A,
  ranges_from_b L Asan_top = true ->
  H_off_segments Tgt_zlib_uncompress_fuzzer_asan_loaded_segments (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan_segs_below HL). Qed.

(* [comment removed for export] *)
Definition Both_top : Z := 0x67f000%Z.
Lemma Both_wx_nowrap : wx_segs_nowrap TgtO_zlib_uncompress_fuzzer_both_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Both_segs_below : segs_below_b TgtO_zlib_uncompress_fuzzer_both_loaded_segments Both_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Both_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Both_top <= bv_unsigned a)%Z) ->
  H_off_segments TgtO_zlib_uncompress_fuzzer_both_loaded_segments H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Both_segs_below Ha). Qed.
Lemma Both_H_off_mkH : forall L A,
  ranges_from_b L Both_top = true ->
  H_off_segments TgtO_zlib_uncompress_fuzzer_both_loaded_segments (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Both_segs_below HL). Qed.

