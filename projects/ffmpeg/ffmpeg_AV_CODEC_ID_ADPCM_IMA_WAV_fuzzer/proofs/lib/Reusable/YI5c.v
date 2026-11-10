(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI5c.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: sk_read is 0, the value the read field of both static FILEs of the image holds; the image links no __stdio_read. *)
(* Modified by Trevor Hansen, 2026-11: copied from projects/zlib/checksum_fuzzer/proofs/lib/Reusable/YI5c.v for ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer, with its module paths changed, and its addresses and numbers named by Reusable/YAddr.v, which holds this fuzz target's plain binary's values; musl's vmlock, which this binary's __vm_wait reads and zlib's binary does not link, added to the static memory the proofs track, and the proofs extended to it. *)
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YO0i YO0f YO0d.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YN03.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YH00 YH03 YH02.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YI16 YI06 YI14 YI5b.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.ffmpeg.ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer.lib.Reusable Require Import YAddr.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
#[global] Instance src0_sink : sink_syms := {|
sk_ofl_lock := src0_D_ofl_lock;
sk_threaded := src0_D_libc + 1;
sk_read := 0;
sk_write := src0_A_stdio_write;
sk_seek := src0_A_stdio_seek;
sk_close := src0_A_stdio_close;
sk_path_addr := src0_D_str_tmp_out_gif;
sk_mode_addr := src0_D_str_wb;
sk_trailer_addr := src0_D_str_3;
sk_rwa_addr := src0_D_str_rwa;
sk_highs_addr := src0_D_const_HIGHS_0x8080808080808080;
sk_ones_addr := src0_D_const_ONES_0x0101010101010100
|}.
Lemma src0_env_addr_range : forall a, env_addr a -> (AX_page_ro) <= a < (AX_page_end).
Proof.
intros a Ha. unfold env_addr in Ha.
cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_path_addr sk_mode_addr sk_trailer_addr sk_rwa_addr sk_highs_addr sk_ones_addr src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc
src0_D_str_tmp_out_gif src0_D_str_wb src0_D_str_3 src0_D_str_rwa src0_D_const_HIGHS_0x8080808080808080 src0_D_const_ONES_0x0101010101010100] in Ha. lia.
Qed.
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma src0_sink_in_img : forall a, (AX_page_data) <= a < (AX_page_end) -> in_img src0_msyms a.
Proof. intros a Ha. apply (covered_sound src0_msyms (AX_page_data) LX_data); [vm_compute; reflexivity | lia]. Qed.
Lemma src0_sink_ro_img : forall a, (AX_page_ro) <= a < (AX_page_text) -> in_img src0_msyms a.
Proof. intros a Ha. apply (covered_sound src0_msyms (AX_page_ro) LX_ro); [vm_compute; reflexivity | lia]. Qed.
Ltac src0_static_tac :=
unfold static_owned, errno_addr; cbn;
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes,
src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_vmlock, src0_D_malloc_context, CTX_SIZE, src0_tp; repeat split; intros H; lia.
#[global] Instance src0_sink_laws : sink_laws src0_msyms.
Proof.
constructor.
- intros a Ha. unfold env_addr in Ha.
cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_path_addr sk_mode_addr sk_trailer_addr sk_rwa_addr sk_highs_addr sk_ones_addr src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc
src0_D_str_tmp_out_gif src0_D_str_wb src0_D_str_3 src0_D_str_rwa src0_D_const_HIGHS_0x8080808080808080 src0_D_const_ONES_0x0101010101010100] in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]]].
+ split; [apply src0_sink_in_img; lia | src0_static_tac].
+ split; [apply src0_sink_in_img; lia | src0_static_tac].
+ split; [apply src0_sink_in_img; lia | src0_static_tac].
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
+ split; [apply src0_sink_ro_img; lia | src0_static_tac].
- intros a Ha. unfold errno_addr in Ha. cbn in Ha. unfold src0_tp in Ha.
split; [apply src0_sink_in_img; lia | src0_static_tac].
Qed.
End b.
