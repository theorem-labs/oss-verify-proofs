(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YI5c.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH00.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YH03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YH02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI16.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YI14.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YI5b.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
#[global] Instance src0_sink : sink_syms := {|
sk_ofl_lock := src0_D_ofl_lock;
sk_threaded := src0_D_libc + 1;
sk_read := src0_A_stdio_read;
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
Lemma src0_env_addr_range : forall a, env_addr a -> 0x10000 <= a < 0x51000.
Proof.
intros a Ha. unfold env_addr in Ha.
cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_path_addr sk_mode_addr sk_trailer_addr sk_rwa_addr sk_highs_addr sk_ones_addr src0_sink src0_sink_head src0_D_ofl_head src0_D_ofl_lock src0_D_libc
src0_D_str_tmp_out_gif src0_D_str_wb src0_D_str_3 src0_D_str_rwa src0_D_const_HIGHS_0x8080808080808080 src0_D_const_ONES_0x0101010101010100] in Ha. lia.
Qed.
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma src0_sink_in_img : forall a, 0x1f000 <= a < 0x51000 -> in_img src0_msyms a.
Proof. intros a Ha. apply (covered_sound src0_msyms 0x1f000 0x32000); [vm_compute; reflexivity | lia]. Qed.
Lemma src0_sink_ro_img : forall a, 0x10000 <= a < 0x12000 -> in_img src0_msyms a.
Proof. intros a Ha. apply (covered_sound src0_msyms 0x10000 0x2000); [vm_compute; reflexivity | lia]. Qed.
Ltac src0_static_tac :=
unfold static_owned, errno_addr; cbn;
unfold src0_D_malloc_lock, src0_D_libc, src0_D_got_stack_chk_guard, src0_D_stack_chk_guard, src0_D_debruijn32, src0_D_size_classes,
src0_D_small_cnt_tab, src0_D_med_cnt_tab, src0_D_malloc_context, CTX_SIZE, src0_tp; repeat split; intros H; lia.
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
