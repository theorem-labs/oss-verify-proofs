(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI06 YI14 UI5b.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
#[global] Instance ubs0_sink : sink_syms := {|
sk_ofl_lock := ubs0_D_ofl_lock;
sk_threaded := ubs0_D_libc + 1;
sk_read := ubs0_A_stdio_read;
sk_write := ubs0_A_stdio_write;
sk_seek := ubs0_A_stdio_seek;
sk_close := ubs0_A_stdio_close;
sk_path_addr := ubs0_D_str_tmp_out_gif;
sk_mode_addr := ubs0_D_str_wb;
sk_trailer_addr := ubs0_D_str_3;
sk_rwa_addr := ubs0_D_str_rwa;
sk_highs_addr := ubs0_D_const_HIGHS_0x8080808080808080;
sk_ones_addr := ubs0_D_const_ONES_0x0101010101010100
|}.
Lemma ubs0_env_addr_range : forall a, env_addr a -> 0x10000 <= a < 0x52000.
Proof.
intros a Ha. unfold env_addr in Ha.
cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_path_addr sk_mode_addr sk_trailer_addr sk_rwa_addr sk_highs_addr sk_ones_addr ubs0_sink ubs0_sink_head ubs0_D_ofl_head ubs0_D_ofl_lock ubs0_D_libc
ubs0_D_str_tmp_out_gif ubs0_D_str_wb ubs0_D_str_3 ubs0_D_str_rwa ubs0_D_const_HIGHS_0x8080808080808080 ubs0_D_const_ONES_0x0101010101010100] in Ha. lia.
Qed.
Section b.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma ubs0_sink_in_img : forall a, 0x20000 <= a < 0x52000 -> in_img ubs0_msyms a.
Proof using. intros a Ha. apply (covered_sound ubs0_msyms 0x20000 0x32000); [vm_compute; reflexivity | lia]. Qed.
Lemma ubs0_sink_ro_img : forall a, 0x10000 <= a < 0x12000 -> in_img ubs0_msyms a.
Proof using. intros a Ha. apply (covered_sound ubs0_msyms 0x10000 0x2000); [vm_compute; reflexivity | lia]. Qed.
Ltac ubs0_static_tac :=
unfold static_owned, errno_addr; cbn;
unfold ubs0_D_malloc_lock, ubs0_D_libc, ubs0_D_got_stack_chk_guard, ubs0_D_stack_chk_guard, ubs0_D_debruijn32, ubs0_D_size_classes,
ubs0_D_small_cnt_tab, ubs0_D_med_cnt_tab, ubs0_D_malloc_context, CTX_SIZE, ubs0_tp; repeat split; intros H; lia.
#[global] Instance ubs0_sink_laws : sink_laws ubs0_msyms.
Proof using.
constructor.
- intros a Ha. unfold env_addr in Ha.
cbv [sk_ofl_head sk_threaded sk_ofl_lock sk_path_addr sk_mode_addr sk_trailer_addr sk_rwa_addr sk_highs_addr sk_ones_addr ubs0_sink ubs0_sink_head ubs0_D_ofl_head ubs0_D_ofl_lock ubs0_D_libc
ubs0_D_str_tmp_out_gif ubs0_D_str_wb ubs0_D_str_3 ubs0_D_str_rwa ubs0_D_const_HIGHS_0x8080808080808080 ubs0_D_const_ONES_0x0101010101010100] in Ha.
destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]]]]].
+ split; [apply ubs0_sink_in_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_in_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_in_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_ro_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_ro_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_ro_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_ro_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_ro_img; lia | ubs0_static_tac].
+ split; [apply ubs0_sink_ro_img; lia | ubs0_static_tac].
- intros a Ha. unfold errno_addr in Ha. cbn in Ha. unfold ubs0_tp in Ha.
split; [apply ubs0_sink_in_img; lia | ubs0_static_tac].
Qed.
End b.
